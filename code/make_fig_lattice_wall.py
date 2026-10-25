#!/usr/bin/env python
"""
Figure 3 for articles/theory/latex/note_v3.tex (2026-10-24, A3).

fig3_lattice_vs_wall.pdf :
  (a) meridian half-plane (s, z) of shell k = 6: the circles of the A2 lattice weight (one point per latitude circle;
      spacing ~ s_k = 8) against the circles of the AR-029 ring weight, which lie on one surface Sigma_6 at mesh ~3
      (a co-dimension-one wall at every scale above 3);
  (b) the scale-invariant Poincare constant as a Neumann eigenvalue: lambda_1 rho^2 for the lattice weight on
      axis-centred balls (k = 8, rho = s_k .. 8 s_k) stays at ~0.65 of the Lebesgue value 4.33, while for the wall
      weight (alpha = 2, ball at z0 = 256 crossed by Sigma_8) it halves with every doubling of rho (~ rho^{-(alpha-1)}).
All numbers are recomputed from the check scripts (a2_scattered_weight.py, a_gate_ring_weight.py,
a2_poincare_eigen.py); nothing is typed in by hand.  Palette: as make_figures.py (dataviz reference instance).
"""
import math, os, sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = HERE
FIGDIR = os.path.normpath(os.path.join(HERE, "..", "figures"))
sys.path.insert(0, CHECKS)
from scattered_weight import LatticeWeight, circles_in_shell, shell_params           # noqa: E402
from ring_weight import RingWeight, rings, rho_k                                   # noqa: E402
from poincare_eigen import axisym_ball_lambda1                                         # noqa: E402

C1, C2, C3, C4 = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"
INK, INK2, GRID = "#0b0b0b", "#52514e", "#d9d8d3"
plt.rcParams.update({
    "font.family": "serif", "font.serif": ["cmr10", "DejaVu Serif"], "mathtext.fontset": "cm",
    "axes.unicode_minus": False, "axes.formatter.use_mathtext": True,
    "font.size": 8, "axes.titlesize": 8.5, "axes.labelsize": 8, "legend.fontsize": 7.5,
    "xtick.labelsize": 7.5, "ytick.labelsize": 7.5,
    "axes.edgecolor": INK2, "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.5, "axes.axisbelow": True,
    "lines.linewidth": 1.3, "pdf.fonttype": 42,
})

def panel_title(ax, text):
    ax.set_title(text, loc="left", color=INK, pad=6)

def main():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.6), gridspec_kw={"width_ratios": [1.0, 1.15]})

    # ---------------- (a) geometry of shell k = 6 in the meridian half-plane
    k = 6
    r, th, _ = circles_in_shell(k)
    ax1.scatter(r * np.sin(th), r * np.cos(th), s=5, color=C1, label="lattice weight: one point per circle", zorder=3)
    S, Z = rings(k)
    sel = (np.hypot(S, Z) >= 2.0 ** k) & (np.hypot(S, Z) < 2.0 ** (k + 1))
    ax1.scatter(S[sel], Z[sel], s=2.5, color=C2, label="ring weight: circles on one surface $\\Sigma_6$", zorder=2)
    tt = np.linspace(0, math.pi, 400)
    for rr in (2.0 ** k, 2.0 ** (k + 1)):
        ax1.plot(rr * np.sin(tt), rr * np.cos(tt), color=GRID, lw=0.8, zorder=1)
    rho = rho_k(k, tt)
    ax1.plot(rho * np.sin(tt), rho * np.cos(tt), color=C2, lw=0.6, alpha=0.5, zorder=1)
    ax1.set_aspect("equal")
    ax1.set_xlim(0, 2.0 ** (k + 1) * 1.02); ax1.set_ylim(-2.0 ** (k + 1) * 1.02, 2.0 ** (k + 1) * 1.02)
    ax1.set_xlabel("$s=r\\sin\\theta$"); ax1.set_ylabel("$z=r\\cos\\theta$")
    ax1.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), frameon=False, handletextpad=0.3, borderaxespad=0.0)
    panel_title(ax1, "(a) the shell $2^6\\leq r<2^7$")

    # ---------------- (b) Poincare constants as Neumann eigenvalues
    alpha = 4.0
    k8 = 8
    W = LatticeWeight(alpha, k8 + 2)
    s8 = 2.0 ** (k8 / 2.0); z0 = 1.5 * 2.0 ** k8
    fs = [1.0, 2.0, 4.0, 8.0]
    lat, leb = [], []
    for f in fs:
        rho_b = f * s8
        l, _, _ = axisym_ball_lambda1(W.w_sz, z0, rho_b, 0.5)
        l1, _, _ = axisym_ball_lambda1(lambda S_, Z_: np.ones_like(S_), z0, rho_b, 0.5)
        lat.append(l * rho_b ** 2); leb.append(l1 * rho_b ** 2)
    R = RingWeight(2.0, 10)
    rhos_w = [8.0, 16.0, 32.0, 64.0]
    wall = []
    for rho_b in rhos_w:
        l, _, _ = axisym_ball_lambda1(R.f, 256.0, rho_b, 0.25 if rho_b <= 16 else 0.5)
        wall.append(l * rho_b ** 2)
    x_lat = np.array(fs) * s8
    ax2.plot(x_lat, lat, "o-", color=C1, label="lattice weight, $\\alpha=4$, balls centred on the axis")
    ax2.plot(rhos_w, wall, "s-", color=C2, label="ring weight, $\\alpha=2$, balls crossed by $\\Sigma_8$")
    ax2.plot(x_lat, leb, "--", color=INK2, lw=0.9, label="Lebesgue control ($\\lambda_1\\rho^2\\to4.33$)")
    ax2.plot(rhos_w, wall[0] * (np.array(rhos_w) / rhos_w[0]) ** (-1.0), ":", color=C2, lw=0.9, label="$\\propto\\rho^{-(\\alpha-1)}$")
    ax2.set_xscale("log", base=2); ax2.set_yscale("log")
    ax2.set_xlabel("ball radius $\\rho$ (lattice: $\\rho/s_8=1,2,4,8$)"); ax2.set_ylabel("$\\lambda_1(B)\\,\\rho^2$")
    ax2.set_ylim(0.08, 8)
    ax2.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), frameon=False, handletextpad=0.4, borderaxespad=0.0, ncol=2)
    panel_title(ax2, "(b) Poincar$\\acute{\\mathrm{e}}$ constant $1/(\\lambda_1\\rho^2)$")

    fig.tight_layout(w_pad=1.5, rect=(0, 0.02, 1, 1))
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(FIGDIR, "fig3_lattice_vs_wall." + ext), dpi=200 if ext == "png" else None)
    print("lattice lambda1 rho^2:", ["%.3f" % v for v in lat], " lebesgue:", ["%.3f" % v for v in leb])
    print("wall    lambda1 rho^2:", ["%.4f" % v for v in wall])

if __name__ == "__main__":
    main()
