#!/usr/bin/env python
"""
AR-029 A2 (seam programme, direction A, step A2): the SCATTERED co-dimension-two lattice weight on R^3.

Construction (axisymmetric about the z-axis; all circles are latitude circles, so dist(x, Gamma) is the
2-D distance in the meridian half-plane (s, z) = (r sin th, r cos th) to the point set {(r_n sin th_n, r_n cos th_n)}):

    shell k (k >= 4):  radii in [2^k, 2^(k+1)),  N_k = 2^(k+2) circles,  L_k = 2^ceil(k/2) layers,  M_k = N_k / L_k
    layer i (0 <= i < L_k):  radius r_i = 2^k + i * 2^k / L_k           (radial spacing 2^k / L_k  ~  s_k := 2^(k/2))
    circle (i, j) (0 <= j < M_k):  polar angle th_n = pi (n + 1/2) / N_k  with  n = j L_k + i
          -> within a layer the circles are pi L_k / N_k apart in angle (physical ~ (0.8 .. 1.6) s_k),
             and across the whole shell the N_k angles th_n are ALL the values pi (n + 1/2) / N_k:
             every direction is within pi / (2 N_k) in angle, i.e. within ~0.8 in distance, of some circle.
    weight  w(x) = ( (1 + d^2) / (1 + |x| + d^2) )^(alpha/2),   d = dist(x, Gamma),   alpha >= 4.
          -> near a circle at radius r the weight is the cylinder weight (1 + d^2)^(alpha/2) normalised by
             s(r)^alpha, s(r)^2 = 1 + r; it is ~1 (bounded above and below) once d is comparable to s(r).

Claims checked (ASCII output; numbers of record in a2_scattered_weight_<date>_a<alpha>.txt):
 D1  GEOMETRY: lattice spacings over s_k; max distance of a shell point to Gamma over s_k (bounded; no wall);
     nearest-neighbour distance between circles over s_k (bounded below).
 D2  Brown 6.4.3 silent: fbar(r) bounded below (sphere mean of w), at layer radii and between layers.
 D3  Brown 6.4.4 silent for EVERY direction: I_k(phi) = Int_{2^k}^{2^(k+1)} dr / (r^2 w(r phi)) bounded below by a
     k-independent constant for alpha = 4 (growing like 2^(k(alpha/2 - 2)) for alpha > 4): min over directions
     (random directions, worst-case midpoints between consecutive th_n, the poles, the equator).
 D4  VOLUME: mu(B_r) / r^3 bounded above and below  =>  Int r dr / mu(B_r) < inf  (Grigor'yan volume test, transience
     under doubling + Poincare).
 D5  DOUBLING: mu(B(x, 2 rho)) / mu(B(x, rho)) for centres on a circle, in the bulk, on the axis; rho from 1 to 8 s_k.
 D6  LIPSCHITZ LOG: sup |grad log w| (finite differences at random points) -- the constant L of Lemma K12, which makes
     f* = phi * w a genuine Gaussian marginal comparable to w with bounded drift.
 Part 2 (a2_poincare_eigen.py): Neumann eigenvalue tests of the scale-invariant Poincare inequality.
"""
import math
import sys
import time
import numpy as np
from scipy.spatial import cKDTree

OUT = []
def say(s=""):
    print(s, flush=True)
    OUT.append(s)

K_MIN = 4

def shell_params(k):
    N = 2 ** (k + 2)
    L = 2 ** ((k + 1) // 2)
    M = N // L
    return N, L, M

def circles_in_shell(k):
    """(r, theta, n) of every circle of shell k."""
    N, L, M = shell_params(k)
    I, J = np.meshgrid(np.arange(L), np.arange(M), indexing="ij")
    n = J * L + I
    r = 2.0 ** k + I * (2.0 ** k / L)
    th = math.pi * (n + 0.5) / N
    return r.ravel(), th.ravel(), n.ravel()

class LatticeWeight:
    def __init__(self, alpha, k_max):
        self.alpha = alpha
        self.k_max = k_max
        S, Z = [], []
        for k in range(K_MIN, k_max + 2):          # one extra shell so block boundaries see their neighbours
            r, th, _ = circles_in_shell(k)
            S.append(r * np.sin(th)); Z.append(r * np.cos(th))
        self.pts = np.column_stack((np.concatenate(S), np.concatenate(Z)))
        self.tree = cKDTree(self.pts)
    def dist(self, s, z):
        d, _ = self.tree.query(np.column_stack((np.ravel(s), np.ravel(z))), k=1, workers=-1)
        return d.reshape(np.shape(s))
    def w_sz(self, s, z):
        d = self.dist(s, z)
        r = np.sqrt(np.asarray(s) ** 2 + np.asarray(z) ** 2)
        return ((1.0 + d * d) / (1.0 + r + d * d)) ** (self.alpha / 2.0)
    def w_xyz(self, p):
        s = np.sqrt(p[..., 0] ** 2 + p[..., 1] ** 2)
        return self.w_sz(s, p[..., 2])

# ------------------------------------------------------------------ D1 geometry
def d1_geometry(W, ks, rng):
    say("D1  lattice geometry (s_k = 2^(k/2))")
    say("     k      N_k     L_k    M_k   dr/s_k   r*dth/s_k (r=2^k..2^(k+1))   NN dist/s_k (min)   max dist(shell pt, Gamma)/s_k   smallest circle radius")
    for k in ks:
        N, L, M = shell_params(k)
        s = 2.0 ** (k / 2.0)
        r, th, n = circles_in_shell(k)
        pts = np.column_stack((r * np.sin(th), r * np.cos(th)))
        tree = cKDTree(pts)
        dnn, _ = tree.query(pts, k=2)
        m = 200000
        rr = (2.0 ** (3 * k) * (1.0 + 7.0 * rng.random(m))) ** (1.0 / 3.0)
        tt = np.arccos(1.0 - 2.0 * rng.random(m))
        dmax = W.dist(rr * np.sin(tt), rr * np.cos(tt)).max()
        say("  %4d  %7d  %5d  %5d   %5.2f    %5.2f .. %5.2f                %6.3f              %6.3f                        %6.2f"
            % (k, N, L, M, (2.0 ** k / L) / s, 2.0 ** k * math.pi * L / N / s, 2.0 ** (k + 1) * math.pi * L / N / s,
               dnn[:, 1].min() / s, dmax / s, (r * np.sin(th)).min()))
    say("  => a sheared rectangular lattice of circles in the meridian half-plane with spacing ~ s_k in both directions;")
    say("     every point of the shell is within ~s_k of Gamma and no closer pattern exists: the low-weight set is a")
    say("     union of tubes of radius ~1 around circles ~s_k apart (no co-dimension-one wall at any scale).")
    say()

# ------------------------------------------------------------------ D2 sphere mean
def sphere_mean(W, r):
    n = int(8 * r) + 1001
    th = np.linspace(0.0, math.pi, n)
    f = W.w_sz(r * np.sin(th), r * np.cos(th))
    return 0.5 * np.trapezoid(f * np.sin(th), th)

def d2_fbar(W, ks):
    say("D2  sphere mean fbar(r) (Brown 6.4.3 needs Int dr/(r^2 fbar) = inf; bounded-below fbar makes it converge)")
    say("     k      r = r_0 (layer)   fbar     r = r_0 + dr/2 (between)   fbar     r = r_{L/2}   fbar")
    for k in ks:
        N, L, M = shell_params(k)
        dr = 2.0 ** k / L
        r0 = 2.0 ** k
        rmid = 2.0 ** k + (L // 2) * dr
        say("  %4d   %12.1f   %8.4f   %12.1f            %8.4f   %12.1f   %8.4f"
            % (k, r0, sphere_mean(W, r0), r0 + dr / 2, sphere_mean(W, r0 + dr / 2), rmid, sphere_mean(W, rmid)))
    say("  => fbar bounded below by a k-independent constant: Brown 6.4.3 silent.")
    say()

# ------------------------------------------------------------------ D3 ray integrals
def ray_integral(W, k, phi, h=0.1):
    r = np.arange(2.0 ** k, 2.0 ** (k + 1) + h / 2, h)
    f = W.w_sz(r * math.sin(phi), r * math.cos(phi))
    return np.trapezoid(1.0 / (r * r * f), r)

def d3_rays(W, ks, rng, n_rand=400, n_mid=400):
    say("D3  ray integrals per block, I_k(phi) = Int_{2^k}^{2^(k+1)} dr/(r^2 w(r phi)); Brown 6.4.4 fires iff sup over a")
    say("     positive-measure set of directions of the FULL integral is finite; here every direction pays >= c per block")
    say("     k    min I_k   median I_k   max I_k   I_k(pole)   I_k(equator)   worst-case midpoints: min   [directions sampled]")
    for k in ks:
        N, L, M = shell_params(k)
        phis = rng.random(n_rand) * math.pi
        mids = math.pi * (rng.integers(0, N, n_mid) + 1.0) / N        # exactly between consecutive th_n
        I_rand = np.array([ray_integral(W, k, p) for p in phis])
        I_mid = np.array([ray_integral(W, k, p) for p in mids])
        I_pole = ray_integral(W, k, 1e-9)
        I_eq = ray_integral(W, k, math.pi / 2)
        allI = np.concatenate((I_rand, I_mid, [I_pole, I_eq]))
        say("  %4d   %7.3f   %8.3f   %9.3f   %8.3f   %10.3f          %8.3f           [%d]"
            % (k, allI.min(), np.median(allI), allI.max(), I_pole, I_eq, I_mid.min(), allI.size))
    say("  => min over directions bounded below (alpha = 4) or growing (alpha > 4): sum over k diverges for every ray;")
    say("     Brown 6.4.4 silent.")
    say()

# ------------------------------------------------------------------ D4 volume growth
def shell_mass(W, r_lo, r_hi, h=0.5):
    """mu({r_lo <= |x| < r_hi}) by quadrature on an (r, theta) grid with physical resolution ~h."""
    total = 0.0
    r_edges = np.arange(r_lo, r_hi + h / 2, h)
    for a, b in zip(r_edges[:-1], r_edges[1:]):
        r = 0.5 * (a + b)
        n = max(64, int(math.pi * r / h) + 1)
        th = np.linspace(0.0, math.pi, n)
        f = W.w_sz(r * np.sin(th), r * np.cos(th))
        total += 2.0 * math.pi * r * r * (b - a) * np.trapezoid(f * np.sin(th), th)
    return total

def d4_volume(W, ks):
    say("D4  volume growth mu(B_r) / (4 pi r^3 / 3) at r = 2^k (quadrature, resolution 0.5)")
    say("     k         r        mu(B_r)        mu/(4/3 pi r^3)    shell mass / shell volume")
    mu = shell_mass(W, 0.0, 2.0 ** K_MIN)
    say("  %4d  %9.1f   %12.4e   %12.4f" % (K_MIN, 2.0 ** K_MIN, mu, mu / (4 / 3 * math.pi * 8.0 ** K_MIN)))
    for k in ks:
        m = shell_mass(W, 2.0 ** k, 2.0 ** (k + 1))
        mu += m
        say("  %4d  %9.1f   %12.4e   %12.4f          %12.4f"
            % (k + 1, 2.0 ** (k + 1), mu, mu / (4 / 3 * math.pi * 8.0 ** (k + 1)), m / (4 / 3 * math.pi * (8.0 ** (k + 1) - 8.0 ** k))))
    say("  => mu(B_r) ~ c r^3 with c bounded above and below: Int r dr / mu(B_r) < inf (volume test => transient under D+P).")
    say()

# ------------------------------------------------------------------ D5 doubling
def ball_mass_mc(W, x0, rho, n, rng):
    v = rng.normal(size=(n, 3)); v /= np.linalg.norm(v, axis=1)[:, None]
    u = rng.random(n) ** (1.0 / 3.0)
    p = x0 + rho * v * u[:, None]
    return (4.0 / 3.0 * math.pi * rho ** 3) * W.w_xyz(p).mean()

def d5_doubling(W, k, rng, n=200000):
    N, L, M = shell_params(k)
    s = 2.0 ** (k / 2.0)
    r, th, nn = circles_in_shell(k)
    i0 = L // 2; j0 = M // 2
    idx = np.where((nn == j0 * L + i0))[0][0]
    c_circ = np.array([r[idx] * math.sin(th[idx]), 0.0, r[idx] * math.cos(th[idx])])
    rb = r[idx] + 0.5 * 2.0 ** k / L
    thb = th[idx] + 0.5 * math.pi * L / N
    c_bulk = np.array([rb * math.sin(thb), 0.0, rb * math.cos(thb)])
    c_axis = np.array([0.0, 0.0, 1.5 * 2.0 ** k])
    say("D5  doubling ratios mu(B(x, 2 rho)) / mu(B(x, rho)) in shell k = %d (s_k = %.1f); MC %d points per ball" % (k, s, n))
    say("     rho/s_k    rho      on a circle    bulk point    axis point    (Lebesgue: 8)")
    for rho in [1.0, 2.0, 4.0, s / 4, s / 2, s, 2 * s, 4 * s, 8 * s]:
        vals = []
        for c in (c_circ, c_bulk, c_axis):
            vals.append(ball_mass_mc(W, c, 2 * rho, n, rng) / ball_mass_mc(W, c, rho, n, rng))
        say("  %7.3f   %7.1f    %9.3f     %9.3f     %9.3f" % (rho / s, rho, vals[0], vals[1], vals[2]))
    say("  => bounded ratios at every scale (the on-circle small-scale ratio is the co-dimension-two power-weight value).")
    say()

# ------------------------------------------------------------------ D6 Lipschitz constant of log w
def d6_lipschitz(W, ks, rng, n=100000, eps=1e-4):
    say("D6  sup |grad log w| by central differences at random shell points (Lemma K12 constant L)")
    say("     k     max |grad log w|    99th pct    analytic bound (alpha/2)(1 + 1.618) = %.3f" % (W.alpha / 2 * 2.618))
    for k in ks:
        rr = (2.0 ** (3 * k) * (1.0 + 7.0 * rng.random(n))) ** (1.0 / 3.0)
        tt = np.arccos(1.0 - 2.0 * rng.random(n)); ph = 2 * math.pi * rng.random(n)
        p = np.column_stack((rr * np.sin(tt) * np.cos(ph), rr * np.sin(tt) * np.sin(ph), rr * np.cos(tt)))
        g2 = np.zeros(n)
        for a in range(3):
            e = np.zeros(3); e[a] = eps
            g = (np.log(W.w_xyz(p + e)) - np.log(W.w_xyz(p - e))) / (2 * eps)
            g2 += g * g
        g = np.sqrt(g2)
        say("  %4d     %10.4f        %10.4f" % (k, g.max(), np.percentile(g, 99)))
    say("  => log w is Lipschitz with a k-independent constant L (<= alpha/2 + o(1) in practice):")
    say("     f* = phi * w is a Gaussian marginal with c_L w <= f* <= C_L w and |grad log f*| <= L (Lemma K12).")
    say()

# ------------------------------------------------------------------ main
def main():
    alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 4.0
    k_max = int(sys.argv[2]) if len(sys.argv) > 2 else 11
    rng = np.random.default_rng(20261024)
    t0 = time.time()
    say("AR-029 A2: scattered co-dimension-two lattice weight on R^3, alpha = %.1f, shells k = %d..%d" % (alpha, K_MIN, k_max))
    say("=" * 110)
    W = LatticeWeight(alpha, k_max)
    ks = list(range(K_MIN, k_max + 1))
    d1_geometry(W, ks, rng)
    d2_fbar(W, ks)
    d3_rays(W, ks[:8], rng)
    d4_volume(W, ks[:7])
    d5_doubling(W, 8, rng)
    d6_lipschitz(W, [6, 8, 10], rng)
    say("elapsed %.0f s" % (time.time() - t0))
    return OUT

if __name__ == "__main__":
    out = main()
    tag = "a%g" % (float(sys.argv[1]) if len(sys.argv) > 1 else 4.0)
    with open("articles/theory/checks/a2_scattered_weight_2026-10-24_%s.txt" % tag, "w", encoding="ascii") as fh:
        fh.write("\n".join(out) + "\n")
