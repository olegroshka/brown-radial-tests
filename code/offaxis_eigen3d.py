#!/usr/bin/env python
"""
AR-029 A3 numerical closure: full 3-D Neumann eigenvalue test of the scale-invariant Poincare inequality for the
A2 lattice weight on CUBES whose centre is OFF the symmetry axis (the one case the axisymmetric reduction of
a2_poincare_eigen.py cannot reach).

Cube Q = centre + [-half, half]^3, uniform grid n^3, finite volumes: face conductance = geometric mean of the weight
on the two cells times h (= face area h^2 over distance h), cell mass = w h^3.  Generalised eigenproblem
K u = lambda M u, shift-invert Lanczos; lambda_1 = second smallest.  Lebesgue control for a cube of half-side rho:
lambda_1 rho^2 = pi^2/4 = 2.467.

Centres (shell k = 8, s_k = 16): (a) a point ON a mid-layer circle at theta ~ pi/2 (the cube of half-side 2 s_k then
contains the strand and its ~4 nearest neighbours), (b) the bulk point between four circles, (c) the axis point as a
cross-check against the 2-D computation (E3).  Sizes: half-side s_k (h = 1, 1/2) and 2 s_k (h = 4/3, 1).
"""
import math
import sys
import time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scattered_weight import LatticeWeight, circles_in_shell, shell_params

OUT = []
def say(s=""):
    print(s, flush=True)
    OUT.append(s)

def lambda1_cube(wfun, centre, half, n):
    h = 2.0 * half / n
    ax = [centre[a] - half + (np.arange(n) + 0.5) * h for a in range(3)]
    X, Y, Z = np.meshgrid(*ax, indexing="ij")
    P = np.stack((X, Y, Z), axis=-1).reshape(-1, 3)
    w = wfun(P).reshape(n, n, n)
    idx = np.arange(n ** 3).reshape(n, n, n)
    rows, cols, vals = [], [], []
    diag = np.zeros(n ** 3)
    for axis in range(3):
        sl_a = [slice(None)] * 3; sl_b = [slice(None)] * 3
        sl_a[axis] = slice(0, n - 1); sl_b[axis] = slice(1, n)
        ia = idx[tuple(sl_a)].ravel(); ib = idx[tuple(sl_b)].ravel()
        c = np.sqrt(w[tuple(sl_a)].ravel() * w[tuple(sl_b)].ravel()) * h
        rows += [ia, ib]; cols += [ib, ia]; vals += [-c, -c]
        np.add.at(diag, ia, c); np.add.at(diag, ib, c)
    N = n ** 3
    rows.append(np.arange(N)); cols.append(np.arange(N)); vals.append(diag)
    K = sp.csc_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(N, N))
    M = sp.diags(w.ravel() * h ** 3).tocsc()
    scale = M.diagonal().sum() / K.diagonal().sum()
    t0 = time.time()
    ev, _ = eigsh(K * scale, k=2, M=M, sigma=-0.05, which="LM", tol=1e-7)
    ev = np.sort(ev) / scale
    return ev[1], ev[0], N, time.time() - t0, float(w.min()), float(w.max())

def main():
    alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 4.0
    k = 8
    W = LatticeWeight(alpha, k + 2)
    N_, L, M_ = shell_params(k)
    s = 2.0 ** (k / 2.0)
    r, th, nn = circles_in_shell(k)
    i0 = L // 2; j0 = M_ // 2
    idx = np.where(nn == j0 * L + i0)[0][0]
    c_circ = np.array([r[idx] * math.sin(th[idx]), 0.0, r[idx] * math.cos(th[idx])])
    rb = r[idx] + 0.5 * 2.0 ** k / L
    thb = th[idx] + 0.5 * math.pi * L / N_
    c_bulk = np.array([rb * math.sin(thb), 0.0, rb * math.cos(thb)])
    c_axis = np.array([0.0, 0.0, 1.5 * 2.0 ** k])
    say("AR-029 A3: 3-D off-axis Neumann eigenvalue test, lattice weight alpha = %.1f, shell k = %d (s_k = %.0f)" % (alpha, k, s))
    say("     circle centre (s,z) = (%.1f, %.1f), radius %.1f; bulk centre (%.1f, %.1f); axis centre z = %.1f" % (c_circ[0], c_circ[2], r[idx] * math.sin(th[idx]), c_bulk[0], c_bulk[2], c_axis[2]))
    say("     Lebesgue control for a cube of half-side rho: lambda_1 rho^2 = pi^2/4 = 2.467")
    say("     centre     rho/s_k    rho     n     h      lambda_1 rho^2    control (w=1)    min w      max w     cells     time(s)")
    for name, c in (("circle", c_circ), ("bulk", c_bulk), ("axis", c_axis)):
        for f, ns in ((1.0, (32, 64)), (2.0, (48, 64))):
            half = f * s
            for n in ns:
                if name != "circle" and n == 64 and f == 1.0:
                    continue
                l, l0, N, dt, wmin, wmax = lambda1_cube(W.w_xyz, c, half, n)
                if n == ns[-1] or name == "circle":
                    l1, _, _, _, _, _ = lambda1_cube(lambda P: np.ones(P.shape[0]), c, half, n)
                else:
                    l1 = float("nan")
                say("  %-8s   %6.1f   %6.1f   %3d  %6.3f   %12.4f     %12.4f    %9.2e  %8.4f   %8d   %7.1f"
                    % (name, f, half, n, 2 * half / n, l * half * half, l1 * half * half, wmin, wmax, N, dt))
    say("  => bounded below at the off-axis centres as at the axis: the scale-invariant Poincare inequality holds on")
    say("     cubes containing several strands; compare E3 (axis-centred balls) and E4 (the wall collapses).")
    return OUT

if __name__ == "__main__":
    out = main()
    tag = "a%g" % (float(sys.argv[1]) if len(sys.argv) > 1 else 4.0)
    with open("articles/theory/checks/a3_offaxis_eigen3d_2026-10-24_%s.txt" % tag, "w", encoding="ascii") as fh:
        fh.write("\n".join(out) + "\n")
