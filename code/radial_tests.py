#!/usr/bin/env python
"""
AR-028 gate G0 — numerical companion to the spherical-A2 lemma.

Weights are functions of x_1 only on R^3 (product priors F = F_1 x Lebesgue(R^2)):
    w_log (t) = (1+|t|)^-1 log(e+|t|)      -- the candidate Brown-undecided example
    w_half(t) = (1+|t|)^-1/2               -- an A2-type control (decided by Brown 6.4.4)
    w_one (t) = (1+|t|)^-1                 -- borderline control (decided by Brown 6.4.3)

Part A: sphere averages on S^2 at radius r (u = cos(angle) uniform on [-1,1]):
    fbar(r) = (1/2) Int w(r u) du,   A(r) = (1/2) Int du / w(r u)   (mean of 1/f*),
    spherical-A2 ratio Q(r) = fbar(r) A(r),
    I_S(R)  = Int_1^R dr / (4 pi r^2 fbar)           Brown 6.4.3 (diverges => recurrent/admissible),
    M(R)    = Int_1^R A(r) dr / r^2                   direction-averaged ray integral
                                                      (finite => a.e. ray finite => Brown 6.4.4 applies),
    I_V(R)  = Int_1^R r dr / V(r), V(r) = Int_0^r 4 pi s^2 fbar(s) ds   (volume test).
Lemma (proved in the packet): if sup_r Q(r) < inf then M <= C I_S, so I_S < inf forces Brown 6.4.4
and I_S = inf is Brown 6.4.3: Brown's radial tests are exhaustive on spherical-A2 weights.

Part B: 1-D heat kernel of the diffusion with generator (1/w)(w u')' for w_log, density w.r.t. w dx,
Crank-Nicolson, geometric time steps.  Product transience criterion for W x BM(R^2):
    Int^inf p_t^{(1)}(0,0) dt / (4 pi t) < inf.
Scaling prediction: p_t^{(1)}(0,0) ~ c log^2 t / t   (vs the naive 1/log^2 t), so the integral converges.
Control: w == 1 gives p_t(0,0) = (4 pi t)^-1/2.
ASCII-only output.
"""
import math
import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import splu

def w_log(t):  return np.log(math.e + np.abs(t)) / (1.0 + np.abs(t))
def w_half(t): return (1.0 + np.abs(t)) ** -0.5
def w_one(t):  return (1.0 + np.abs(t)) ** -1.0

# ---------------------------------------------------------------- Part A
def sphere_means_grid(w, r):
    """fbar(r) = (1/r) Int_0^r w(t) dt and A(r) = (1/r) Int_0^r dt/w(t) for a weight depending on x_1 only
    (u = cos(angle) is uniform on [-1,1] for S^2, so the sphere mean is the symmetric t-average).
    Exact cumulative trapezoid on [0,1] linear + log grid up to max(r); accurate near the peak at t = 0."""
    t_lin = np.linspace(0.0, 1.0, 2001)
    t_log = np.logspace(0.0, math.log10(r[-1]), 400001)[1:]
    t = np.concatenate((t_lin, t_log))
    wv = w(t)
    cw = np.concatenate(([0.0], np.cumsum(0.5 * (wv[1:] + wv[:-1]) * np.diff(t))))
    ci = np.concatenate(([0.0], np.cumsum(0.5 * (1.0 / wv[1:] + 1.0 / wv[:-1]) * np.diff(t))))
    fbar = np.interp(r, t, cw) / r
    A = np.interp(r, t, ci) / r
    return fbar, A

def part_A(name, w, Rmax=1e8, n=4000):
    r = np.logspace(0.0, math.log10(Rmax), n)
    fbar, A = sphere_means_grid(w, r)
    S = 4.0 * math.pi * r ** 2 * fbar
    # V(r): add the inner ball [0,1] crudely (w ~ w(0) there)
    V = np.concatenate(([0.0], np.cumsum(0.5 * (S[1:] + S[:-1]) * np.diff(r)))) + 4.0 / 3.0 * math.pi * w(0.0)
    I_S = np.concatenate(([0.0], np.cumsum(0.5 * (1.0 / S[1:] + 1.0 / S[:-1]) * np.diff(r))))
    M = np.concatenate(([0.0], np.cumsum(0.5 * (A[1:] / r[1:] ** 2 + A[:-1] / r[:-1] ** 2) * np.diff(r))))
    I_V = np.concatenate(([0.0], np.cumsum(0.5 * (r[1:] / V[1:] + r[:-1] / V[:-1]) * np.diff(r))))
    Q = fbar * A
    print(f"--- {name} ---")
    print(f"{'R':>8} {'Q(R)=fbar*A':>12} {'I_S(R)':>10} {'M(R) rays':>10} {'I_V(R)':>10}")
    for R in (1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8):
        i = np.searchsorted(r, R) - 1
        print(f"{R:8.0e} {Q[i]:12.4g} {I_S[i]:10.4g} {M[i]:10.4g} {I_V[i]:10.4g}")
    return r, Q, I_S, M, I_V

# ---------------------------------------------------------------- Part B
def heat_kernel_1d(w, L=10000.0, dx=0.5, t_end=1e7, dt0=0.02, growth=0.02, report_at=(1e2, 1e3, 1e4, 1e5, 1e6, 1e7)):
    x = np.arange(-L, L + dx / 2, dx)
    N = x.size
    i0 = N // 2
    wx = w(x)
    wh = w(x[:-1] + dx / 2)                      # w at half points
    # conservative symmetric discretisation of (1/w) d/dx (w du/dx)
    lower = wh / (wx[1:] * dx ** 2)             # coefficient of u_{i-1} in row i (i>=1)
    upper = wh / (wx[:-1] * dx ** 2)            # coefficient of u_{i+1} in row i (i<=N-2)
    main = np.zeros(N)
    main[:-1] -= upper
    main[1:] -= lower                           # reflecting boundaries (zero flux)
    Lop = diags([lower, main, upper], [-1, 0, 1], format="csc")
    u = np.zeros(N); u[i0] = 1.0 / (wx[i0] * dx)   # delta, density w.r.t. w dx
    t = 0.0; dt = dt0
    out = {}
    targets = list(report_at)
    I = diags([np.ones(N)], [0], format="csc")
    lu = None; dt_fact = None
    green = 0.0; t_prev = None; u_prev = None
    while t < t_end and targets:
        if dt_fact != dt:
            lu = splu((I - 0.5 * dt * Lop).tocsc()); dt_fact = dt
        rhs = u + 0.5 * dt * (Lop @ u)
        u = lu.solve(rhs)
        t += dt
        if t_prev is not None and t_prev >= 1.0:          # Green integral Int u(t,0)/(4 pi t) dt from t=1
            green += 0.5 * (u[i0] / (4 * math.pi * t) + u_prev / (4 * math.pi * t_prev)) * (t - t_prev)
        t_prev, u_prev = t, u[i0]
        if t >= targets[0]:
            mass = np.sum(u * wx) * dx
            edge = max(u[0], u[-1]) / max(u[i0], 1e-300)
            out[targets[0]] = (t, u[i0], mass, edge, green)
            targets.pop(0)
        dt = max(dt0, growth * t)
    return out

if __name__ == "__main__":
    np.set_printoptions(precision=4)
    print("=" * 78); print("G0 PART A: sphere-average / ray / volume integrals, m = 3, weights w(x_1)"); print("=" * 78)
    print("predictions: w_log -> Q ~ log r/4 (unbounded), I_S converges, M diverges, I_V converges => Brown silent")
    print("             w_half -> Q bounded, I_S converges, M converges => Brown 6.4.4 decides (transient)")
    print("             w_one  -> Q ~ log r (unbounded), I_S diverges => Brown 6.4.3 decides (recurrent)")
    for name, w in (("w_log = (1+|t|)^-1 log(e+|t|)", w_log), ("w_half = (1+|t|)^-1/2", w_half), ("w_one = (1+|t|)^-1", w_one)):
        part_A(name, w)
    print()
    print("=" * 78); print("G0 PART B: 1-D on-diagonal heat kernel p_t(0,0) (density w.r.t. w dx), Crank-Nicolson"); print("=" * 78)
    print("control w == 1: sqrt(t) p_t(0,0) -> (4 pi)^-1/2 = 0.28209")
    res = heat_kernel_1d(lambda t: np.ones_like(np.asarray(t, dtype=float)) if np.ndim(t) else 1.0, t_end=1e5, report_at=(1e2, 1e3, 1e4, 1e5))
    for T, (t, p, mass, edge, g) in res.items():
        print(f"  t={t:9.3g}  sqrt(t)*p = {math.sqrt(t) * p:8.5f}   mass={mass:.4f}  edge/centre={edge:.1e}")
    print("w_log: prediction p_t(0,0) ~ c log^2(t)/t  =>  t*p/log^2 t -> const;  Green integral Int p/(4 pi t) dt converges")
    res = heat_kernel_1d(w_log, t_end=1e7)
    for T, (t, p, mass, edge, g) in res.items():
        print(f"  t={t:9.3g}  p={p:10.3e}  t*p={t * p:9.4f}  t*p/log^2 t={t * p / math.log(t) ** 2:8.5f}  "
              f"log^2(t)*p (naive)={math.log(t) ** 2 * p:9.3e}  Green(1..t)={g:.5f}  mass={mass:.4f}  edge/centre={edge:.1e}")
