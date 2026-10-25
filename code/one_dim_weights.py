#!/usr/bin/env python
"""
AR-028 G0 -- CORRECTION CHECK (2026-10-23).

The G0 packet (ar/AR-028_G0-2026-10-23.md s1, consequence (a)) asserted that T1's hypothesis class
(volume doubling + scale-invariant L^2 Poincare on balls, bounded log-gradient) has bounded spherical
A2 ratio Q(r).  That assertion was never proved.  This script tests it on one-dimensional weights
(product weights w(x_1) dx on R^3: for them the spherical ratio Q(r) is the 1-D A2 ratio of [-r, r],
and doubling / Poincare on cubes of R^3 follow from the 1-D properties by tensorisation).

 (a) doubling:   sup_I mu(2I)/mu(I)  over a grid of intervals I = [c - l/2, c + l/2]  (mu = w dt);
 (b) Poincare:   Muckenhoupt's weighted Hardy inequality (p = 2, same weight both sides):
        for u(xi) = 0,  Int_xi^b u^2 w <= 4 B Int_xi^b u'^2 w,   B = sup_{xi<x<b} mu([x,b]) nu([xi,x]),
        nu = (1/w) dt, symmetrically on the left; the mean minimises the weighted L^2 distance to
        constants, so  Int_I |u - u_I|^2 w <= 4 min_xi max(B_right(xi), B_left(xi)) Int_I u'^2 w.
        Reported: sup_I [4 min_xi max(B_r, B_l)] / |I|^2  (bounded => scale-invariant Poincare holds).
 (c) log-gradient: sup |w'/w|.
 (d) spherical A2 ratio Q(r) = mu([0,r]) nu([0,r]) / r^2 at r = 1e8.
 (e) Lemma K9 quantity  nu([L,2L]) mu([0,L]) / L^2  (bounded under doubling + Poincare by the two-region
     test function; it controls Brown's ray integrals for product weights on R^m, m >= 3).
 (f) consistency of the volume heuristic p_t(0,0) ~ 1/V(sqrt t) with the product-kernel numbers of
     g0_feasibility.py Part B for w_log (not in the doubling class; informational only).

Weights: w_log  = (1+|t|)^-1 log(e+|t|)   Brown-undecided example of the G0 packet
         w_one  = (1+|t|)^-1                borderline
         w_half = (1+|t|)^-1/2              A2
         w_grow = (1+|t|)^2                 doubling + Poincare but NOT A2 (Q ~ r/3): refutes the assertion
         w_two  = (1+|t|)^-2                finite measure (not doubling at large scale)
         w_exp  = exp(-|t|)                 not doubling (control; grid capped at |t| <= 600)
Precision: for intervals much shorter than their distance to 0 the cumulative-difference mu, nu are
replaced by local Simpson sums (no cancellation).  ASCII-only output.
"""
import math
import numpy as np

def w_log(t):  return np.log(math.e + np.abs(t)) / (1.0 + np.abs(t))
def w_half(t): return (1.0 + np.abs(t)) ** -0.5
def w_one(t):  return (1.0 + np.abs(t)) ** -1.0
def w_grow(t): return (1.0 + np.abs(t)) ** 2.0
def w_two(t):  return (1.0 + np.abs(t)) ** -2.0
def w_exp(t):  return np.exp(-np.abs(t))

TMAX = 1e9

class Cum:
    """cumulative integrals of w and 1/w on [0, TMAX], odd extension to R, local Simpson for short intervals."""
    def __init__(self, w):
        self.w = w
        t_lin = np.linspace(0.0, 1.0, 4001)
        t_log = np.logspace(0.0, math.log10(TMAX), 900001)[1:]
        self.t = np.concatenate((t_lin, t_log))
        wv = w(self.t)
        dt = np.diff(self.t)
        self.cw = np.concatenate(([0.0], np.cumsum(0.5 * (wv[1:] + wv[:-1]) * dt)))
        self.ci = np.concatenate(([0.0], np.cumsum(0.5 * (1.0 / wv[1:] + 1.0 / wv[:-1]) * dt)))
    def _W(self, x): return np.sign(x) * np.interp(np.abs(x), self.t, self.cw)
    def _N(self, x): return np.sign(x) * np.interp(np.abs(x), self.t, self.ci)
    def _local(self, g, a, b):
        m = 0.5 * (a + b)
        return (b - a) / 6.0 * (g(a) + 4.0 * g(m) + g(b))
    def mu(self, a, b):
        a = np.asarray(a, dtype=float); b = np.asarray(b, dtype=float)
        short = (a * b > 0) & ((b - a) < 1e-4 * np.minimum(np.abs(a), np.abs(b)))
        return np.where(short, self._local(self.w, a, b), self._W(b) - self._W(a))
    def nu(self, a, b):
        a = np.asarray(a, dtype=float); b = np.asarray(b, dtype=float)
        short = (a * b > 0) & ((b - a) < 1e-4 * np.minimum(np.abs(a), np.abs(b)))
        return np.where(short, self._local(lambda s: 1.0 / self.w(s), a, b), self._N(b) - self._N(a))

def interval_grid(tmax):
    centres = np.concatenate(([0.0], np.logspace(-2, 8, 51), -np.logspace(-2, 8, 51)))
    lengths = np.logspace(-2, 8, 51)
    for c in centres:
        for l in lengths:
            a, b = c - l / 2, c + l / 2
            if max(abs(a), abs(b)) * 4 <= tmax:
                yield a, b

def doubling(C, tmax):
    worst, arg = 0.0, None
    for a, b in interval_grid(tmax):
        c, l = 0.5 * (a + b), b - a
        r = float(C.mu(c - l, c + l) / C.mu(a, b))
        if r > worst: worst, arg = r, (a, b)
    return worst, arg

S_GRID = np.concatenate((np.logspace(-9, -0.30103, 300), 1.0 - np.logspace(-9, -0.30103, 300)))

def hardy_B_right(C, xi, b):
    x = xi + (b - xi) * S_GRID
    return float(np.max(C.mu(x, b) * C.nu(xi, x)))

def hardy_B_left(C, a, xi):
    x = a + (xi - a) * S_GRID
    return float(np.max(C.mu(a, x) * C.nu(x, xi)))

def poincare(C, tmax):
    worst, arg = 0.0, None
    for a, b in interval_grid(tmax):
        l = b - a
        refs = [a, 0.5 * (a + b), b] + ([0.0] if a < 0.0 < b else [])
        best = math.inf
        for xi in refs:
            Br = hardy_B_right(C, xi, b) if xi < b else 0.0
            Bl = hardy_B_left(C, a, xi) if xi > a else 0.0
            best = min(best, 4.0 * max(Br, Bl))
        val = best / l ** 2
        if val > worst: worst, arg = val, (a, b)
    return worst, arg

def loggrad(w, tmax):
    t = np.logspace(-3, math.log10(tmax), 200001)
    h = 1e-4 * np.maximum(t, 1.0)
    d = (np.log(w(t + h)) - np.log(w(t - h))) / (2 * h)
    return float(np.max(np.abs(d)))

def volume3(w, r):
    """V(r) = Int_{-r}^{r} w(s) pi (r^2 - s^2) ds for the product weight on R^3."""
    s = np.concatenate((np.linspace(0.0, 1.0, 2001), np.logspace(0.0, math.log10(r), 200001)[1:]))
    wv = w(s)
    return 2.0 * math.pi * (r * r * np.trapezoid(wv, s) - np.trapezoid(wv * s * s, s))

if __name__ == "__main__":
    weights = [("w_log", w_log, TMAX), ("w_one", w_one, TMAX), ("w_half", w_half, TMAX),
               ("w_grow", w_grow, TMAX), ("w_two", w_two, TMAX), ("w_exp", w_exp, 600.0)]
    print("=" * 96)
    print("G0 CORRECTION CHECK: doubling / Poincare / log-gradient / spherical A2 / Lemma K9, 1-D weights")
    print("=" * 96)
    print("%-7s %10s %10s %9s %11s %12s %12s" % ("weight", "dbl(1e4)", "dbl(1e8)", "PI/|I|^2", "sup|w'/w|", "Q(1e8)", "K9(1e8)"))
    print("%-7s %10s %10s %9s %11s %12s %12s" % ("", "sup ratio", "sup ratio", "sup", "", "mu nu/r^2", "nu mu/L^2"))
    for name, w, tmax in weights:
        C = Cum(w)
        d4, _ = doubling(C, min(tmax, 4e4))
        d8, darg = doubling(C, tmax)
        p, parg = poincare(C, tmax)
        g = loggrad(w, tmax)
        R = min(1e8, tmax / 4)
        Q = float(C.mu(0.0, R) * C.nu(0.0, R) / R ** 2)
        L = R / 2
        K9 = float(C.nu(L, 2 * L) * C.mu(0.0, L) / L ** 2)
        print("%-7s %10.4g %10.4g %9.4g %11.4g %12.4g %12.4g" % (name, d4, d8, p, g, Q, K9))
        print("        worst doubling I = [%.3g, %.3g];  worst Poincare I = [%.3g, %.3g]"
              % (darg[0], darg[1], parg[0], parg[1]))
    print()
    print("Scale dependence of the doubling ratio and of K9 (growth => not doubling / rays expensive):")
    print("%-7s" % "weight" + "".join("%12s" % ("r=1e%d" % k) for k in range(2, 9)))
    for name, w, tmax in weights[:4]:
        C = Cum(w)
        row = []
        for k in range(2, 9):
            r = 10.0 ** k
            row.append(float(C.mu(0.0, 2 * r) / C.mu(0.5 * r, 1.5 * r)))   # I = [r/2, 3r/2], 2I = [0, 2r]
        print("%-7s" % (name + " dbl") + "".join("%12.4g" % v for v in row))
        row = []
        for k in range(2, 9):
            L = 10.0 ** k
            row.append(float(C.nu(L, 2 * L) * C.mu(0.0, L) / L ** 2))
        print("%-7s" % (name + " K9") + "".join("%12.4g" % v for v in row))
    print()
    print("(f) volume heuristic vs product-kernel numbers (w_log on R^3; informational, w_log is not doubling):")
    print("%10s %12s %14s %18s" % ("t", "p_t(0,0)", "V(sqrt t)", "p_t(0,0)*V(sqrt t)"))
    partB = {1e3: 2.58, 1e4: 2.95, 1e5: 3.18, 1e6: 3.33, 1e7: 3.44}   # log^2(t) p_t^W(0,0) from Part B
    for t, c in partB.items():
        p = (c / math.log(t) ** 2) / (4 * math.pi * t)
        V = volume3(w_log, math.sqrt(t))
        print("%10.0e %12.4g %14.4g %18.4g" % (t, p, V, p * V))
    print()
    print("Reading.  w_log and w_one: doubling ratio grows like log r (not doubling) -> outside T1's class;")
    print("w_half: doubling, Poincare, A2 (Q bounded).  w_grow: doubling + Poincare with Q ~ r/3 unbounded ->")
    print("the packet's assertion 'T1-class => bounded spherical A2 ratio' is FALSE as stated.  The K9 quantity")
    print("is bounded exactly for the doubling + Poincare weights, as Lemma K9 predicts.")
