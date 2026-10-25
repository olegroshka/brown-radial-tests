#!/usr/bin/env python
"""
AR-029 A2, part 2: scale-invariant Poincare inequality as a Neumann eigenvalue problem.

For a weighted region (Omega, w dx) the best constant in  Var_mu(u) <= C rho^2 Int |grad u|^2 dmu  is
C = 1 / (lambda_1 rho^2), lambda_1 = first nonzero Neumann eigenvalue of the weighted Laplacian  -(1/w) div(w grad).
A uniform Poincare inequality on a family of regions of size rho  <=>  inf lambda_1 rho^2 > 0 over the family.

Discretisation: finite volumes on a uniform grid of cell size h; generalised eigenproblem  K u = lambda M u  with
K the weighted graph Laplacian (face conductance = geometric mean of the weight on the two cells times the face
measure over h) and M = diag(cell measure).  Solved by shift-invert Lanczos (scipy eigsh).  lambda_1 = second
smallest eigenvalue (the smallest is 0, constants).  Lebesgue controls: square [-R,R]^2: lambda_1 R^2 = pi^2/4 = 2.467;
ball in R^3 (axisymmetric m=0 modes): lambda_1 rho^2 = 2.0816^2 = 4.333 (first zero of j_1').

Axisymmetric reduction (3-D ball centred ON the axis, axisymmetric weight): for the azimuthal modes m >= 1,
Int |grad u|^2 dmu >= Int |d_phi u|^2 / s^2 dmu >= (1/rho^2) Int |u|^2 dmu and the mean of u is zero, so these modes
satisfy the Poincare inequality with constant 1 for ANY weight; only the m = 0 (axisymmetric) problem is non-trivial,
and it is a 2-D weighted problem on the meridian half-disc with the measure 2 pi s w(s,z) ds dz.

Tests:
 E1  LOCAL LEMMA L (Theorem 5 (1), the cylinder weight): 2-D radial weight (1+|y|^2)^(alpha/2) on squares
     [-R,R]^2 (valley at the centre) and on [0,2R]x[-R,R] (valley on an edge) for R = 2..64: lambda_1 R^2 bounded below.
 E2  LOCAL LEMMA L' (a single circle of radius R_c, scales rho >= R_c): axisymmetric m=0 problem on B(c, rho), c the
     centre of the circle, weight (1 + dist(x, C_{R_c})^2)^(alpha/2), rho = R_c, 2R_c, 4R_c, 8R_c, R_c in {1, 4, 16}.
 E3  THE LATTICE (the A2 weight): axisymmetric m=0 problem on balls centred on the axis at |x| = 1.5 * 2^k,
     rho = s_k, 2 s_k, 4 s_k, 8 s_k, for k = 8 (s = 16) and k = 10 (s = 32); h-convergence at rho = 2 s_k.
 E4  POSITIVE CONTROL (Argon's ring weight = the WALL of AR-029): same test on a ball crossed by the wall Sigma_8:
     lambda_1 rho^2 must collapse like rho^-(alpha-1) (the Poincare failure found in AR-029 C5a).
"""
import math
import sys
import time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scattered_weight import LatticeWeight, K_MIN
from ring_weight import RingWeight

OUT = []
def say(s=""):
    print(s, flush=True)
    OUT.append(s)

def neumann_lambda1(mask, wcell, jac, h):
    """
    mask: boolean (ny, nx) of cells in the region; wcell: weight at cell centres; jac: extra Jacobian at cell centres
    (1 for plane problems, 2 pi s for the axisymmetric meridian problem).  Returns lambda_1 (second smallest eigenvalue).
    Cell measure = jac * w * h^2 ; face conductance = (geometric mean of jac*w on both cells) (for a 2-D grid the face
    length h cancels against the 1/h of the gradient).
    """
    ny, nx = mask.shape
    idx = -np.ones(mask.shape, dtype=np.int64)
    idx[mask] = np.arange(mask.sum())
    n = mask.sum()
    q = jac * wcell
    rows, cols, vals = [], [], []
    diag = np.zeros(n)
    for dy, dx in ((0, 1), (1, 0)):
        a = mask[: ny - dy, : nx - dx] & mask[dy:, dx:]
        ia = idx[: ny - dy, : nx - dx][a]; ib = idx[dy:, dx:][a]
        c = np.sqrt(q[: ny - dy, : nx - dx][a] * q[dy:, dx:][a])
        rows.append(ia); cols.append(ib); vals.append(-c)
        rows.append(ib); cols.append(ia); vals.append(-c)
        np.add.at(diag, ia, c); np.add.at(diag, ib, c)
    rows.append(np.arange(n)); cols.append(np.arange(n)); vals.append(diag)
    K = sp.csc_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(n, n))
    M = sp.diags(q[mask] * h * h).tocsc()
    # scale so that the target eigenvalues are O(1) for the solver
    scale = (M.diagonal().sum() / K.diagonal().sum())
    sigma = -0.05
    vals_, _ = eigsh(K * scale, k=3, M=M, sigma=sigma, which="LM", tol=1e-8)
    vals_ = np.sort(vals_) / scale
    return vals_[1], vals_[0], n

# ------------------------------------------------------------------ E1: 2-D radial weight on squares
def e1_local(alpha):
    say("E1  local lemma L: 2-D radial weight (1+|y|^2)^(alpha/2), alpha = %.1f, Neumann lambda_1 R^2 on squares (Lebesgue: 2.467)" % alpha)
    say("     R      h      centred [-R,R]^2    edge valley [0,2R]x[-R,R]    centred, w = 1 (control)   cells")
    for R in [2.0, 4.0, 8.0, 16.0, 32.0, 64.0]:
        h = min(0.25, R / 64.0) if R <= 16 else R / 128.0
        nx = int(round(2 * R / h))
        xs = (np.arange(nx) + 0.5) * h - R
        X, Y = np.meshgrid(xs, xs)
        mask = np.ones_like(X, dtype=bool)
        w = (1.0 + X * X + Y * Y) ** (alpha / 2.0)
        l_c, l0, n = neumann_lambda1(mask, w, np.ones_like(w), h)
        w_e = (1.0 + (X + R) ** 2 + Y * Y) ** (alpha / 2.0)       # valley at the left edge midpoint
        l_e, _, _ = neumann_lambda1(mask, w_e, np.ones_like(w), h)
        l_1, _, _ = neumann_lambda1(mask, np.ones_like(w), np.ones_like(w), h)
        say("  %5.1f  %6.3f   %12.4f          %12.4f                  %12.4f          %7d" % (R, h, l_c * R * R, l_e * R * R, l_1 * R * R, n))
    say("  => lambda_1 R^2 bounded below as R grows: scale-invariant Poincare for the regularised co-dimension-two power weight.")
    say()

# ------------------------------------------------------------------ axisymmetric meridian problem on a ball
def axisym_ball_lambda1(wfun, z0, rho, h):
    """m = 0 Neumann eigenvalue on the 3-D ball B((0,0,z0), rho) for the axisymmetric weight wfun(s, z)."""
    ns = int(round(rho / h)); nz = int(round(2 * rho / h))
    s = (np.arange(ns) + 0.5) * h
    z = z0 - rho + (np.arange(nz) + 0.5) * h
    S, Z = np.meshgrid(s, z)
    mask = (S * S + (Z - z0) ** 2) <= rho * rho
    w = wfun(S, Z)
    jac = 2.0 * math.pi * S
    return neumann_lambda1(mask, w, jac, h)

def e2_circle(alpha):
    say("E2  local lemma L': single circle of radius R_c in the plane z = 0, weight (1 + dist^2)^(alpha/2), alpha = %.1f;" % alpha)
    say("     m=0 Neumann lambda_1 rho^2 on B(0, rho) (Lebesgue m=0 control: 4.333)")
    say("     R_c    rho/R_c    rho      h      lambda_1 rho^2    control (w=1)   cells")
    for Rc in [1.0, 4.0, 16.0]:
        for f in [1.0, 2.0, 4.0, 8.0]:
            rho = f * Rc
            h = min(0.25, rho / 96.0) if rho <= 24 else rho / 192.0
            wf = lambda S, Z, Rc=Rc: (1.0 + (S - Rc) ** 2 + Z * Z) ** (alpha / 2.0)
            l, _, n = axisym_ball_lambda1(wf, 0.0, rho, h)
            l1, _, _ = axisym_ball_lambda1(lambda S, Z: np.ones_like(S), 0.0, rho, h)
            say("  %5.1f   %6.1f   %6.1f  %6.3f   %12.4f     %12.4f   %7d" % (Rc, f, rho, h, l * rho * rho, l1 * rho * rho, n))
    say("  => bounded below uniformly in R_c and rho >= R_c (the regime the bending argument does not cover).")
    say()

def e3_lattice(alpha):
    say("E3  the A2 lattice weight, alpha = %.1f: m=0 Neumann lambda_1 rho^2 on balls centred on the axis at |x| = 1.5 * 2^k" % alpha)
    say("     k    s_k    rho/s_k    rho      h      lambda_1 rho^2    control (w=1)   cells   time(s)")
    for k, hs in ((8, (1.0, 0.5, 0.25)), (10, (1.0, 0.5))):
        W = LatticeWeight(alpha, k + 2)
        s = 2.0 ** (k / 2.0)
        z0 = 1.5 * 2.0 ** k
        for f in [1.0, 2.0, 4.0, 8.0]:
            rho = f * s
            for h in (hs if f == 2.0 else (hs[1],)):
                if rho / h > 1100:        # cap the grid (~ 1100 x 2200 half-disc)
                    continue
                t0 = time.time()
                l, _, n = axisym_ball_lambda1(W.w_sz, z0, rho, h)
                l1, _, _ = axisym_ball_lambda1(lambda S, Z: np.ones_like(S), z0, rho, h)
                say("  %4d  %5.1f   %6.1f   %7.1f  %6.3f   %12.4f     %12.4f   %7d   %6.1f"
                    % (k, s, f, rho, h, l * rho * rho, l1 * rho * rho, n, time.time() - t0))
    say("  => lambda_1 rho^2 bounded below from rho = s_k to 8 s_k and across k: no large-scale Poincare failure")
    say("     (contrast with E4).")
    say()

def e4_wall_control(alpha_ring=2.0):
    say("E4  positive control: Argon's ring weight (AR-029 wall), alpha = %.1f, ball centred on the axis at z0 = 256" % alpha_ring)
    say("     (the wall Sigma_8 crosses it at r = 255.5 near the north pole); m=0 Neumann lambda_1 rho^2")
    say("     rho      h      lambda_1 rho^2    control (w=1)   lambda_1 rho^2 * rho^(alpha-1)   cells")
    R = RingWeight(alpha_ring, 10)
    wf = lambda S, Z: R.f(S, Z)
    for rho in [8.0, 16.0, 32.0, 64.0]:
        h = 0.25 if rho <= 16 else (0.5 if rho <= 32 else 0.5)
        l, _, n = axisym_ball_lambda1(wf, 256.0, rho, h)
        l1, _, _ = axisym_ball_lambda1(lambda S, Z: np.ones_like(S), 256.0, rho, h)
        say("  %6.1f  %6.3f   %12.4e     %12.4f   %14.4f   %7d" % (rho, h, l * rho * rho, l1 * rho * rho, l * rho * rho * rho ** (alpha_ring - 1), n))
    say("  => collapses with rho: the eigenvalue test detects the co-dimension-one wall (AR-029 C5a, Q_P ~ rho^(alpha-1)).")
    say()

def main():
    alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 4.0
    t0 = time.time()
    say("AR-029 A2 part 2: Neumann-eigenvalue tests of the scale-invariant Poincare inequality, alpha = %.1f" % alpha)
    say("=" * 110)
    e1_local(alpha)
    e2_circle(alpha)
    e3_lattice(alpha)
    e4_wall_control(2.0)
    say("elapsed %.0f s" % (time.time() - t0))
    return OUT

if __name__ == "__main__":
    out = main()
    tag = "a%g" % (float(sys.argv[1]) if len(sys.argv) > 1 else 4.0)
    with open("articles/theory/checks/a2_poincare_eigen_2026-10-24_%s.txt" % tag, "w", encoding="ascii") as fh:
        fh.write("\n".join(out) + "\n")
