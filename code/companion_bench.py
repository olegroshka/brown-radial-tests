#!/usr/bin/env python
"""
Numbers behind the test bench of the companion guide (companion/explainer.html, Section 15): Brown's sphere test,
Brown's ray test, the ball probe and the true resistance on the paper's two priors, both symmetric about the z-axis
and computed in the meridian half-plane (s, z) = (r sin theta, r cos theta).

    lattice: the scattered-circles weight of Theorem B, alpha = 4   (scattered_weight.py)
    ring:    the wall weight of Proposition 5.2, alpha = 2          (ring_weight.py)

 B1  sphere sum (1/4pi) int_8^R dr / (r^2 fbar(r)) and min fbar on [16, 512]      (Brown's sphere test)
 B2  ray tolls int over shell k of dr / (r^2 w) over 721 directions, k = 4..8      (Brown's ray test)
 B3  V(r) / (4/3 pi r^3) at r = 2^K                                              (the volume count)
 B4  lambda_1 rho^2 of the m = 0 Neumann problem on axis-centred balls             (the ball probe)
 B5  sphere bound, true resistance and ray bound from the ball B_8 to the sphere of radius 2^K, K = 5..10, on a polar
     network in the half-plane (radial step 1, 3216 angles); the two bounds are the network with every ring shorted
     and with every angular link cut, so Rayleigh's law guarantees sphere <= true <= ray.
ASCII output to results/companion_bench.txt.
"""
import math, os, sys, time
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import spsolve, eigsh
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scattered_weight import LatticeWeight
from ring_weight import RingWeight

OUT = []
def say(s=""):
    print(s, flush=True); OUT.append(s)

def fbar(w, r):
    n = int(8 * r) + 1001
    th = np.linspace(0.0, math.pi, n)
    return 0.5 * np.trapezoid(w(r * np.sin(th), r * np.cos(th)) * np.sin(th), th)

def radial(name, w):
    rs = np.arange(0.25, 512.0 + 1e-9, 0.25)
    fb = np.array([fbar(w, r) for r in rs])
    S = 4 * math.pi * rs ** 2 * fb
    V = np.concatenate(([0.0], np.cumsum(0.5 * (S[1:] + S[:-1]) * np.diff(rs)))) + (4 / 3) * math.pi * rs[0] ** 3 * fb[0]
    m = rs >= 8.0
    Isph = np.concatenate(([0.0], np.cumsum(0.5 * (1 / S[m][1:] + 1 / S[m][:-1]) * np.diff(rs[m]))))
    say("B1  %s: min fbar on [16, 512] = %.4f; sphere sum from 8 to 2^K:" % (name, fb[rs >= 16].min()))
    say("    " + "  ".join("K=%d %.4f" % (K, np.interp(2.0 ** K, rs[m], Isph)) for K in range(4, 10)))
    ths = np.linspace(0.0, math.pi, 721); rr = np.arange(8.0, 512.0 + 1e-9, 0.1)
    tol = {k: [] for k in range(4, 9)}
    for th in ths:
        g = 1.0 / (rr * rr * w(rr * math.sin(th), rr * math.cos(th)))
        I = np.concatenate(([0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * 0.1)))
        for k in tol:
            tol[k].append(I[int(round((2 ** (k + 1) - 8) / 0.1))] - I[int(round((2 ** k - 8) / 0.1))])
    say("B2  %s: ray toll per shell over 721 directions (min / median / max):" % name)
    for k, v in tol.items():
        say("    k=%d  %.3f / %.3f / %.3f" % (k, np.min(v), np.median(v), np.max(v)))
    say("B3  %s: V(r)/(4/3 pi r^3): " % name + "  ".join("r=%d %.4f" % (2 ** K, np.interp(2.0 ** K, rs, V) / (4 / 3 * math.pi * 8.0 ** K)) for K in range(5, 10)))

def probe(name, w, z0):
    from poincare_eigen import axisym_ball_lambda1
    vals = []
    for rho in (8.0, 16.0, 32.0, 64.0):
        l, _, _ = axisym_ball_lambda1(w, z0, rho, min(0.5, rho / 64.0))
        vals.append(l * rho * rho)
    say("B4  %s: lambda_1 rho^2 on balls centred on the axis at z = %d, rho = 8, 16, 32, 64: %s   (empty ball 4.333)"
        % (name, z0, ", ".join("%.3f" % v for v in vals)))

def network(w, R, DR=1.0, NTH=3216, RE=8.0):
    NS = int(round((R - RE) / DR)); dth = math.pi / NTH
    thn = (np.arange(NTH) + 0.5) * dth; the = (np.arange(NTH - 1) + 1.0) * dth
    rm = RE + (np.arange(NS) + 0.5) * DR
    Rm, Tn = np.meshgrid(rm, thn, indexing="ij")
    grad = w(Rm * np.sin(Tn), Rm * np.cos(Tn)) * 2 * math.pi * Rm * np.sin(Tn) * Rm * dth / DR      # radial links
    Ri, Te = np.meshgrid(RE + np.arange(1, NS) * DR, the, indexing="ij")
    gang = w(Ri * np.sin(Te), Ri * np.cos(Te)) * 2 * math.pi * np.sin(Te) * DR / dth                 # angular links
    n = (NS - 1) * NTH; idx = np.arange(n).reshape(NS - 1, NTH)
    diag = grad[:-1] + grad[1:]; diag[:, :-1] += gang; diag[:, 1:] += gang
    rows = [idx.ravel()]; cols = [idx.ravel()]; vals = [diag.ravel()]
    for a, b, g in ((idx[:-1].ravel(), idx[1:].ravel(), grad[1:-1].ravel()), (idx[:, :-1].ravel(), idx[:, 1:].ravel(), gang.ravel())):
        rows += [a, b]; cols += [b, a]; vals += [-g, -g]
    A = sp.csc_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(n, n))
    rhs = np.zeros((NS - 1, NTH)); rhs[0] = grad[0]                       # ball B_8 at voltage 1, outer sphere grounded
    u = spsolve(A, rhs.ravel(), permc_spec="MMD_AT_PLUS_A").reshape(NS - 1, NTH)
    true = 1.0 / float(np.sum(grad[0] * (1.0 - u[0])))
    return float(np.sum(1.0 / grad.sum(axis=1))), true, float(1.0 / np.sum(1.0 / np.sum(1.0 / grad, axis=0)))

def truth(name, w):
    say("B5  %s: resistance from B_8 to the sphere of radius 2^K   (sphere bound <= true <= ray bound)" % name)
    for K in range(5, 11):
        t0 = time.time(); a, b, c = network(w, 2.0 ** K)
        say("    K=%2d  sphere %.4f   true %.4f   ray %.4f   (%.0f s)" % (K, a, b, c, time.time() - t0))

def main():
    t0 = time.time()
    say("Companion guide, Section 15: the test bench on the paper's two priors"); say("=" * 78)
    lat, ring = LatticeWeight(4.0, 10).w_sz, RingWeight(2.0, 10).f
    for name, w in (("lattice", lat), ("ring", ring)): radial(name, w)
    probe("lattice", lat, 96.0); probe("ring", ring, 128.0)
    for name, w in (("lattice", lat), ("ring", ring)): truth(name, w)
    say("elapsed %.0f s" % (time.time() - t0))
    os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results"), exist_ok=True)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "companion_bench.txt"), "w", encoding="ascii") as fh:
        fh.write("\n".join(OUT) + "\n")

if __name__ == "__main__":
    main()
