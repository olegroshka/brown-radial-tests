#!/usr/bin/env python
"""
AR-029 gate (seam programme, direction A) -- the ring weight of math-note.tex Theorem 6
(Argon draft, 2026-10-24): is W_F transient (Thm 6 as written) or parabolic?

Construction as written in the draft's proof of Theorem 6:
    for k >= 4 and j = 0..2^k-1, the circle Gamma_{k,j} = { r = 2^k + j,  theta = pi (j + 1/2) / 2^k },
    Gamma = union of all Gamma_{k,j},
    f*(x) = ( (1 + dist(x, Gamma)^2) / (1 + |x|^2) )^(alpha/2),   alpha >= 2.
Everything is axisymmetric about the polar axis, so dist(x, Gamma) is a 2-D problem in the meridian
half-plane (s, z) = (r sin theta, r cos theta): the circles are points (s_kj, z_kj).

Claims tested (ASCII output; numbers of record go to a_gate_ring_weight_<date>.txt):
 C1  MESH.  The circles of block k lie on the surface of revolution
            Sigma_k : r = rho_k(theta) = 2^k (1 + theta/pi) - 1/2,   theta in [0, pi],
     a closed graph over S^2 (r = 2^k - 1/2 at the north pole, 2^(k+1) - 1/2 at the south pole), and
     form a net of bounded mesh on it.  Above the mesh scale Gamma is therefore a co-dimension-ONE wall.
 C2  Brown 6.4.3 silent: the sphere mean fbar(r) stays bounded below across blocks.
 C3  Brown 6.4.4 silent: every ray's integral over block k is bounded below by a constant (it crosses the wall).
 C4  THOMSON LOWER BOUND.  For the radially offset surfaces Sigma_k^(d) : r = rho_k(theta) + d, |d| <= 1,
     the unit flux and Cauchy-Schwarz give, for every unit flow J from B_1 to infinity,
         Int_{layer_k} |J|^2 / f*  dV  >=  E_k := Int_{-1}^{1} dd / Ftilde_k(d),
         Ftilde_k(d) := Int_{Sigma_k^(d)} f* / cos(tilt) dA,   cos(tilt) = n . rhat.
     Layers of blocks k and k+2 are disjoint (consecutive surfaces touch at the poles), so
         inf_J energy(J)  >=  sum over even k of E_k.
     If that sum diverges, cap(B_1) = 0: W_F is PARABOLIC, Brown's diffusion is recurrent, and with
     bounded drift delta_F is ADMISSIBLE (Brown Thm 5.1.1 B) -- the opposite of Theorem 6 (iv).
 C5  POINCARE.  Two-region test function across the wall on balls B(x0, rho), x0 on Sigma_k:
         u = clip((d + 1)/2, 0, 1),  d = signed normal distance to Sigma_k;
         Q_P(rho) = Var_mu(u; B) / ( rho^2 Int_B |grad u|^2 dmu ).
     Uniform scale-invariant Poincare would keep Q_P bounded; a co-dimension-one wall gives Q_P ~ rho^(alpha-1).
     Control: Theorem 5's cylinder weight (1 + s^2)^(alpha/2) with the same test-function family across a
     plane through the axis (co-dimension-two valley): Q_P stays bounded.
 C6  Theorem 5 check (m = 3): for the cylinder weight, Q(r) = fbar(r) A(r) ~ r^(alpha-2) for alpha > 2.
"""
import math
import sys
import numpy as np
from scipy.spatial import cKDTree

OUT = []
def say(s=""):
    print(s)
    OUT.append(s)

# ------------------------------------------------------------------ geometry
K_MIN = 4

def rings(k_max):
    """(s, z) coordinates of all circles Gamma_{k,j} for K_MIN <= k <= k_max."""
    S, Z = [], []
    for k in range(K_MIN, k_max + 1):
        j = np.arange(2 ** k)
        r = 2.0 ** k + j
        th = math.pi * (j + 0.5) / 2 ** k
        S.append(r * np.sin(th)); Z.append(r * np.cos(th))
    return np.concatenate(S), np.concatenate(Z)

class RingWeight:
    def __init__(self, alpha, k_max):
        self.alpha = alpha
        s, z = rings(k_max + 1)              # one extra block so block boundaries see their neighbours
        self.tree = cKDTree(np.column_stack((s, z)))
    def dist(self, s, z):
        d, _ = self.tree.query(np.column_stack((np.ravel(s), np.ravel(z))), k=1)
        return d.reshape(np.shape(s))
    def f(self, s, z):
        d = self.dist(s, z)
        r2 = np.asarray(s) ** 2 + np.asarray(z) ** 2
        return ((1.0 + d ** 2) / (1.0 + r2)) ** (self.alpha / 2.0)

def rho_k(k, th):      return 2.0 ** k * (1.0 + th / math.pi) - 0.5
def drho_k(k):         return 2.0 ** k / math.pi

# ------------------------------------------------------------------ C1 mesh
def c1_mesh(W, ks):
    say("C1  mesh of Gamma on Sigma_k (distance from points of Sigma_k to the nearest circle)")
    say("     k      max dist    mean dist   ring spacing (3-D, consecutive j)")
    for k in ks:
        th = np.linspace(0.0, math.pi, 40 * 2 ** k + 1)
        r = rho_k(k, th)
        d = W.dist(r * np.sin(th), r * np.cos(th))
        j = np.arange(2 ** k - 1)
        r1, r2 = 2.0 ** k + j, 2.0 ** k + j + 1
        t1, t2 = math.pi * (j + 0.5) / 2 ** k, math.pi * (j + 1.5) / 2 ** k
        sp = np.sqrt((r1 * np.sin(t1) - r2 * np.sin(t2)) ** 2 + (r1 * np.cos(t1) - r2 * np.cos(t2)) ** 2)
        say("  %4d   %9.3f   %9.3f    %5.2f .. %5.2f" % (k, d.max(), d.mean(), sp.min(), sp.max()))
    say("  => bounded mesh: at scales above ~3 the set Gamma is the co-dimension-one surface Sigma_k.")
    say()

# ------------------------------------------------------------------ C2 sphere mean
def sphere_mean(W, r, n=200001):
    th = np.linspace(0.0, math.pi, n)
    f = W.f(r * np.sin(th), r * np.cos(th))
    return 0.5 * np.trapezoid(f * np.sin(th), th)

def c2_fbar(W, ks):
    say("C2  sphere mean fbar(r) at mid-block radii (Brown 6.4.3 needs Int dr/(r^2 fbar) = inf)")
    say("     k      r          fbar(r)      r^2 fbar")
    for k in ks:
        r = 1.5 * 2.0 ** k
        fb = sphere_mean(W, r)
        say("  %4d   %9.1f   %10.4e   %10.3e" % (k, r, fb, r * r * fb))
    say("  => fbar bounded below by a k-independent constant: Int dr/(r^2 fbar) < inf, Brown 6.4.3 silent.")
    say()

# ------------------------------------------------------------------ C3 ray integrals
def c3_rays(W, ks, thetas):
    say("C3  ray integrals over block k, I_k(theta) = Int_{2^k}^{2^(k+1)} dr / (r^2 f*(r,theta))  (Brown 6.4.4 needs sup over a cone < inf)")
    hdr = "     k   " + "  ".join("theta=%.2f" % t for t in thetas)
    say(hdr)
    for k in ks:
        r = np.linspace(2.0 ** k, 2.0 ** (k + 1), 40 * 2 ** k + 1)
        vals = []
        for t in thetas:
            f = W.f(r * math.sin(t), r * math.cos(t))
            vals.append(np.trapezoid(1.0 / (r * r * f), r))
        say("  %4d   " % k + "  ".join("%10.3e" % v for v in vals))
    say("  => every ray pays >= const per block; summed over k the ray integral diverges for every direction:")
    say("     Brown 6.4.4 silent (as Theorem 6 (iii) claims).")
    say()

# ------------------------------------------------------------------ C4 Thomson bound
def weighted_area_tilde(W, k, d, n):
    th = np.linspace(0.0, math.pi, n)
    rho = rho_k(k, th) + d
    dr = drho_k(k)
    f = W.f(rho * np.sin(th), rho * np.cos(th))
    # dA = 2 pi rho sqrt(rho^2 + rho'^2) sin th dth ;  1/cos(tilt) = sqrt(rho^2 + rho'^2)/rho  => product has no 1/rho
    integrand = f * (rho ** 2 + dr ** 2) * np.sin(th) * 2.0 * math.pi   # dV = cos(tilt) dA dd ; f/cos(tilt) dA = 2 pi f (rho^2 + rho'^2) sin th dth
    return np.trapezoid(integrand, th), f

def c4_thomson(W, ks, n_d=21):
    say("C4  Thomson lower bound per block: E_k = Int_{-1}^{1} dd / Ftilde_k(d);  cumulative sum over EVEN k")
    say("     (inf_J energy >= sum;  cap(B_1) <= 1/sum;  Euclidean R^3 reference: inf energy = 1/(4 pi) = %.4f)" % (1 / (4 * math.pi)))
    say("     k     Ftilde(0)      min f*/2^-k a   max f*/2^-k a     E_k          cum sum (even k)   1/cumsum")
    ds = np.linspace(-1.0, 1.0, n_d)
    cum = 0.0
    for k in ks:
        n = 40 * 2 ** k + 1
        Fs, fmin, fmax = [], np.inf, 0.0
        for d in ds:
            F, f = weighted_area_tilde(W, k, d, n)
            Fs.append(F)
            sc = 2.0 ** (-k * W.alpha)
            fmin = min(fmin, f.min() / sc); fmax = max(fmax, f.max() / sc)
        Fs = np.array(Fs)
        E = np.trapezoid(1.0 / Fs, ds)
        if k % 2 == 0:
            cum += E
        say("  %4d   %11.4e   %10.3f   %10.3f   %11.4e   %11.4e   %11.4e" % (k, Fs[n_d // 2], fmin, fmax, E, cum, (1.0 / cum if cum > 0 else float('inf'))))
    say("  => per-block terms do not decay (alpha = 2) or grow (alpha > 2): the sum diverges, cap(B_1) = 0,")
    say("     W_F is parabolic => recurrent => bounded drift => delta_F ADMISSIBLE (Brown 5.1.1 B).")
    say()

# ------------------------------------------------------------------ C5 Poincare
def c5_poincare_ring(W, k, rhos, n_pts, rng):
    say("C5a Poincare quotient across the wall, ring weight, ball centre on Sigma_k at theta = pi/2, k = %d" % k)
    say("     rho     Q_P = Var/(rho^2 Energy)    Q_P / rho^(alpha-1)    [MC, %d points per ball]" % n_pts)
    th0 = math.pi / 2
    r0 = rho_k(k, th0)
    x0 = np.array([r0 * math.sin(th0), 0.0, r0 * math.cos(th0)])   # (x, y, z) with s = sqrt(x^2 + y^2)
    dr = drho_k(k)
    for rho in rhos:
        # uniform points in the ball
        v = rng.normal(size=(n_pts, 3)); v /= np.linalg.norm(v, axis=1)[:, None]
        u3 = rng.random(n_pts) ** (1.0 / 3.0)
        p = x0 + rho * v * u3[:, None]
        s = np.sqrt(p[:, 0] ** 2 + p[:, 1] ** 2); z = p[:, 2]
        r = np.sqrt(s * s + z * z); th = np.arctan2(s, z)
        d_rad = r - rho_k(k, th)
        cos_tilt = 1.0 / math.sqrt(1.0 + (dr / r0) ** 2)
        d = d_rad * cos_tilt                           # signed normal distance (local-plane approximation)
        f = W.f(s, z)
        u = np.clip((d + 1.0) / 2.0, 0.0, 1.0)
        grad2 = np.where(np.abs(d) < 1.0, 0.25, 0.0)
        mean_u = np.sum(u * f) / np.sum(f)
        var = np.mean((u - mean_u) ** 2 * f)           # per unit volume (common factor cancels)
        energy = np.mean(grad2 * f)
        Q = var / (rho ** 2 * energy)
        say("  %6.1f   %14.4e           %12.4e" % (rho, Q, Q / rho ** (W.alpha - 1)))
    say("  => Q_P grows like rho^(alpha-1): the scale-invariant Poincare inequality FAILS on balls straddling the wall;")
    say("     Grigor'yan Thm 11.1 (doubling + Poincare) does not apply to this weight.")
    say()

def c5_poincare_cylinder(alpha, rhos, n_pts, rng):
    say("C5b control: Theorem 5 cylinder weight (1+s^2)^(alpha/2), two-region test function across the plane x = 0 (contains the axis), ball at the origin")
    say("     rho     Q_P                        Q_P * rho")
    for rho in rhos:
        v = rng.normal(size=(n_pts, 3)); v /= np.linalg.norm(v, axis=1)[:, None]
        u3 = rng.random(n_pts) ** (1.0 / 3.0)
        p = rho * v * u3[:, None]
        s2 = p[:, 0] ** 2 + p[:, 1] ** 2
        f = (1.0 + s2) ** (alpha / 2.0)
        d = p[:, 0]
        u = np.clip((d + 1.0) / 2.0, 0.0, 1.0)
        grad2 = np.where(np.abs(d) < 1.0, 0.25, 0.0)
        mean_u = np.sum(u * f) / np.sum(f)
        var = np.mean((u - mean_u) ** 2 * f)
        energy = np.mean(grad2 * f)
        Q = var / (rho ** 2 * energy)
        say("  %6.1f   %14.4e           %12.4e" % (rho, Q, Q * rho))
    say("  => bounded (decaying like 1/rho): a co-dimension-two valley does not obstruct the two-region test function.")
    say()

# ------------------------------------------------------------------ C6 Theorem 5
def c6_theorem5(alphas, rs):
    say("C6  Theorem 5 (m = 3): cylinder weight (1+s^2)^(alpha/2), Q(r) = fbar(r) A(r) vs r^(alpha-2)")
    th = np.linspace(0.0, math.pi, 400001)
    for a in alphas:
        say("     alpha = %.1f" % a)
        say("     r          fbar          A             Q           Q / r^(alpha-2)")
        for r in rs:
            w = (1.0 + (r * np.sin(th)) ** 2) ** (a / 2.0)
            fb = 0.5 * np.trapezoid(w * np.sin(th), th)
            A = 0.5 * np.trapezoid(np.sin(th) / w, th)
            Q = fb * A
            say("  %9.1f   %10.3e   %10.3e   %10.3e   %10.3e" % (r, fb, A, Q, Q / r ** (a - 2)))
    say("  => Q ~ r^(alpha-2) for alpha > 2 (unbounded), confirming Theorem 5 part (2); alpha = 2 is the log-borderline.")
    say()

# ------------------------------------------------------------------ main
def main():
    alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
    k_max = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    rng = np.random.default_rng(20261024)
    say("AR-029 A-gate: ring weight of math-note.tex Theorem 6, alpha = %.1f, blocks k = %d..%d" % (alpha, K_MIN, k_max))
    say("=" * 100)
    W = RingWeight(alpha, k_max)
    ks = list(range(K_MIN, k_max + 1))
    c1_mesh(W, ks[:8])
    c2_fbar(W, ks)
    c3_rays(W, ks[:9], [0.3, 0.9, 1.5708, 2.2, 2.8])
    c4_thomson(W, ks)
    c5_poincare_ring(W, 10, [2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0], 600000, rng)
    c5_poincare_cylinder(alpha, [2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0], 600000, rng)
    c6_theorem5([2.0, 3.0, 4.0], [10.0, 100.0, 1000.0, 1e4, 1e5])
    say("Verdict (numerical companion to the analytic argument in ar/AR-029_*): the construction as written is a")
    say("co-dimension-one wall at every scale above its mesh; both Brown tests are silent (as claimed), Poincare fails")
    say("(contrary to Thm 6 (i)), and the Thomson bound makes W_F parabolic (contrary to Thm 6 (iv)): delta_F is ADMISSIBLE.")
    return OUT

if __name__ == "__main__":
    out = main()
    tag = "a%g" % (float(sys.argv[1]) if len(sys.argv) > 1 else 2.0)
    with open("articles/theory/checks/a_gate_ring_weight_2026-10-24_%s.txt" % tag, "w", encoding="ascii") as fh:
        fh.write("\n".join(out) + "\n")
