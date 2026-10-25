#!/usr/bin/env python
"""
Figures for articles/theory/latex/note.tex (2026-10-23).

fig1_geometries.pdf : (a) the pseudosphere = Fisher-Rao geometry of a location-scale family (K = -1 after
                      rescaling; the owner's "horn"), axial coordinate -ln sigma; (b) Komaki's conformal
                      frame of the Stein prior = flat cylinder S^{d-1} x R with the origin at infinite
                      distance (S^{d-1} drawn as a circle); (c) Jacobian eigenvalues of the James-Stein map,
                      tangential eigenvalue vanishing at |x| = sigma sqrt(d-2) (lint check C12).
fig2_undecided.pdf  : (a) Brown's two radial tests and the volume test on the undecided weight
                      w_log(x_1) = (1+|x_1|)^-1 log(e+|x_1|) on R^3 (g0_feasibility.py);
                      (b) doubling ratio mu([0,2r])/mu([r/2,3r/2]) for four 1-D weights;
                      (c) spherical A2 ratio Q(r) for the same weights (g0_doubling_poincare.py).
All numbers are recomputed from the check scripts; nothing is typed in by hand.
Palette: dataviz reference instance (categorical slots 1-4, sequential blue ramp), validated 2026-10-23.
"""
import math, os, sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, Normalize

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = HERE
FIGDIR = os.path.normpath(os.path.join(HERE, "..", "figures"))
sys.path.insert(0, CHECKS)
from radial_tests import w_log, w_half, w_one, sphere_means_grid          # noqa: E402
from one_dim_weights import Cum, w_grow                                 # noqa: E402

# ---------------------------------------------------------------- palette (dataviz reference instance)
C1, C2, C3, C4 = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"      # categorical slots 1-4 (light mode)
INK, INK2, GRID = "#0b0b0b", "#52514e", "#d9d8d3"
SEQ = LinearSegmentedColormap.from_list("seqblue", ["#cde2fb", "#86b6ef", "#3987e5", "#1c5cab", "#0d366b"])

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

def label_end(ax, x, y, text, color, dx=4, dy=0, ha="left", va="center"):
    ax.annotate(text, (x, y), xytext=(dx, dy), textcoords="offset points", color=color,
                fontsize=7.5, ha=ha, va=va)

def panel_title(ax, text):
    ax.set_title(text, loc="left", color=INK, pad=6)

# ================================================================ FIGURE 1: three geometries
def surface(ax, X, Y, Z, C, elev, azim):
    norm = Normalize(vmin=np.min(C), vmax=np.max(C))
    ax.plot_surface(X, Y, Z, facecolors=SEQ(norm(C)), rstride=1, cstride=1, linewidth=0,
                    antialiased=True, shade=True)
    ax.set_axis_off()
    ax.view_init(elev=elev, azim=azim)

def fig1():
    fig = plt.figure(figsize=(7.0, 2.5))
    gs = fig.add_gridspec(1, 3, width_ratios=[1.1, 1.0, 1.05], wspace=0.10, left=0.01, right=0.99,
                          top=0.90, bottom=0.17)
    # (a) pseudosphere: x = sech u cos v, y = sech u sin v, z = u - tanh u ; u = 0 rim (flare), u -> inf cusp
    ax = fig.add_subplot(gs[0], projection="3d")
    u = np.linspace(0.0, 3.6, 110); v = np.linspace(0.0, 2 * np.pi, 84)
    U, V = np.meshgrid(u, v)
    X = np.cosh(U) ** -1 * np.cos(V); Y = np.cosh(U) ** -1 * np.sin(V); Z = U - np.tanh(U)
    surface(ax, Z, X, Y, -U, elev=18, azim=-62)                     # axis along the first plot coordinate
    ax.plot(u - np.tanh(u), 1 / np.cosh(u), np.zeros_like(u), color=INK, lw=0.6, alpha=0.7)   # a meridian
    for u0 in (0.6, 1.6):                                                                  # two parallels
        ax.plot(np.full_like(v, u0 - math.tanh(u0)), np.cos(v) / math.cosh(u0), np.sin(v) / math.cosh(u0),
                color=INK, lw=0.5, alpha=0.5)
    ax.set_box_aspect((2.6, 1.0, 1.0), zoom=1.25)
    ax.text2D(0.02, 0.94, "(a) location$-$scale family (Fisher$-$Rao)", transform=ax.transAxes,
              fontsize=8.5, color=INK)
    ax.text2D(0.03, 0.14, r"flare: $\sigma\to 0$" "\n" r"(high precision)", transform=ax.transAxes,
              fontsize=7.2, color=INK2)
    ax.text2D(0.66, 0.60, r"throat: $\sigma\to\infty$", transform=ax.transAxes, fontsize=7.2, color=INK2)
    ax.text2D(0.03, 0.02, r"axis $u=-\ln\sigma\approx\frac{1}{2}\ln N$: an external clock",
              transform=ax.transAxes, fontsize=7.2, color=INK2)
    # (b) cylinder: S^{d-1} x R, axial coordinate s = (1/2) log |mu|^2, origin at s -> -inf
    ax = fig.add_subplot(gs[1], projection="3d")
    s = np.linspace(-3.0, 3.0, 80); th = np.linspace(0.0, 2 * np.pi, 84)
    S, TH = np.meshgrid(s, th)
    surface(ax, S, np.cos(TH), np.sin(TH), S, elev=18, azim=-62)
    for s0 in (-2.0, 0.0, 2.0):
        ax.plot(np.full_like(th, s0), np.cos(th), np.sin(th), color=INK, lw=0.5, alpha=0.5)
    ax.plot(s, np.ones_like(s), np.zeros_like(s), color=INK, lw=0.6, alpha=0.7)
    ax.set_box_aspect((2.6, 1.0, 1.0), zoom=1.1)
    ax.text2D(0.02, 0.94, "(b) Stein prior in Komaki's frame", transform=ax.transAxes, fontsize=8.5, color=INK)
    ax.text2D(0.02, 0.16, r"$\|\mu\|\to 0$: origin at" "\n" r"infinite distance", transform=ax.transAxes,
              fontsize=7.2, color=INK2)
    ax.text2D(0.76, 0.74, r"$\|\mu\|\to\infty$", transform=ax.transAxes, fontsize=7.2, color=INK2)
    ax.text2D(0.03, 0.02, r"axis $s=\frac{1}{2}\log\|\mu\|^2$; flat $ds^2+d\Omega^2$",
              transform=ax.transAxes, fontsize=7.2, color=INK2)
    # (c) James-Stein Jacobian eigenvalues, d = 3, sigma = 1: 1 -/+ (d-2)/r^2
    ax = fig.add_subplot(gs[2])
    d, sig = 3, 1.0
    r = np.linspace(0.55, 3.5, 400); c = (d - 2) * sig ** 2
    lt, lr = 1 - c / r ** 2, 1 + c / r ** 2
    rh = sig * math.sqrt(d - 2)
    ax.axvline(rh, color=GRID, lw=1.0)
    ax.axhline(0, color=INK2, lw=0.5)
    ax.plot(r, lt, color=C1); ax.plot(r, lr, color=C2)
    label_end(ax, r[-1], lt[-1], "tangential\n$1-(d-2)\\sigma^2/\\|x\\|^2$", C1, dx=-2, dy=-11, ha="right")
    label_end(ax, r[-1], lr[-1], "radial\n$1+(d-2)\\sigma^2/\\|x\\|^2$", C2, dx=-2, dy=8, ha="right")
    ax.annotate(r"$\|x\|=\sigma\sqrt{d-2}$:" "\n" "angular pullback\nmetric degenerates", (rh, 2.0),
                xytext=(14, 6), textcoords="offset points", fontsize=7.2, color=INK2,
                arrowprops=dict(arrowstyle="-", color=INK2, lw=0.5))
    ax.set_xlim(0.5, 3.6); ax.set_ylim(-2.4, 3.3)
    ax.set_xlabel(r"$\|x\|/\sigma$"); ax.set_ylabel("Jacobian eigenvalue", labelpad=2)
    panel_title(ax, "(c) James$-$Stein pullback, $d=3$")
    fig.savefig(os.path.join(FIGDIR, "fig1_geometries.pdf"))
    fig.savefig(os.path.join(FIGDIR, "fig1_geometries.png"), dpi=220)
    plt.close(fig)

# ================================================================ FIGURE 2: the undecided example
def brown_integrals(w, Rmax=1e8, n=4000):
    r = np.logspace(0.0, math.log10(Rmax), n)
    fbar, A = sphere_means_grid(w, r)
    S = 4.0 * math.pi * r ** 2 * fbar
    V = np.concatenate(([0.0], np.cumsum(0.5 * (S[1:] + S[:-1]) * np.diff(r)))) + 4.0 / 3.0 * math.pi * w(0.0)
    I_S = np.concatenate(([0.0], np.cumsum(0.5 * (1.0 / S[1:] + 1.0 / S[:-1]) * np.diff(r))))
    M = np.concatenate(([0.0], np.cumsum(0.5 * (A[1:] / r[1:] ** 2 + A[:-1] / r[:-1] ** 2) * np.diff(r))))
    I_V = np.concatenate(([0.0], np.cumsum(0.5 * (r[1:] / V[1:] + r[:-1] / V[:-1]) * np.diff(r))))
    return r, I_S, M, I_V

def fig2():
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.35))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.86, bottom=0.21, wspace=0.42)
    # (a) Brown's tests on w_log
    ax = axes[0]
    r, I_S, M, I_V = brown_integrals(w_log)
    ax.plot(r, M, color=C2); ax.plot(r, I_V, color=C3); ax.plot(r, I_S, color=C1)
    label_end(ax, r[-1], M[-1], "mean ray integral\n(diverges: 6.4.4 silent)", C2, dx=-3, dy=4, ha="right", va="bottom")
    label_end(ax, r[-1], I_V[-1], "volume test (converges)", C3, dx=-3, dy=5, ha="right", va="bottom")
    i_mid = int(np.searchsorted(r, 3e2))
    label_end(ax, r[i_mid], I_S[i_mid], "sphere test (converges: 6.4.3 silent)", C1, dx=0, dy=-5, ha="left", va="top")
    ax.set_xscale("log"); ax.set_xlim(1, 1e8); ax.set_ylim(0, 3.2)
    ax.set_xlabel(r"$r$"); ax.set_ylabel("partial integral up to $r$", labelpad=2)
    panel_title(ax, "(a) Brown's tests on the undecided weight")
    # (b) doubling ratio, (c) spherical A2 ratio
    weights = [("$(1+|t|)^{-1}\\log(e+|t|)$", w_log, C1), ("$(1+|t|)^{-1}$", w_one, C2),
               ("$(1+|t|)^{-1/2}$", w_half, C3), ("$(1+|t|)^{2}$", w_grow, C4)]
    rr = np.logspace(1, 8, 57)
    axb, axc = axes[1], axes[2]
    place_b = {C1: (-3, -4, "right", "top"), C2: (-3, 3, "right", "bottom"),
               C3: (-3, 4, "right", "bottom"), C4: (-3, -5, "right", "top")}
    place_c = {C1: None, C2: (-3, 4, "right", "bottom"),
               C3: (-3, -4, "right", "top"), C4: (-3, 3, "right", "bottom")}
    for name, w, col in weights:
        C = Cum(w)
        dbl = np.array([float(C.mu(0.0, 2 * x) / C.mu(0.5 * x, 1.5 * x)) for x in rr])
        Q = np.array([float(C.mu(0.0, x) * C.nu(0.0, x) / x ** 2) for x in rr])
        axb.plot(rr, dbl, color=col); axc.plot(rr, Q, color=col)
        dx, dy, ha, va = place_b[col]; label_end(axb, rr[-1], dbl[-1], name, col, dx=dx, dy=dy, ha=ha, va=va)
        if place_c[col] is None:      # leader line into the clear region between the clusters
            i0 = int(np.searchsorted(rr, 1e4))
            axc.annotate(name, (rr[i0], Q[i0]), xytext=(2.5e4, 1.2e3), textcoords="data", color=col,
                         fontsize=7.5, ha="left", va="center",
                         arrowprops=dict(arrowstyle="-", color=col, lw=0.5, shrinkA=0, shrinkB=2))
        else:
            dx, dy, ha, va = place_c[col]; label_end(axc, rr[-1], Q[-1], name, col, dx=dx, dy=dy, ha=ha, va=va)
    axb.set_xscale("log"); axb.set_xlim(10, 1e8); axb.set_ylim(0, 20)
    axb.set_xlabel(r"$r$"); axb.set_ylabel(r"$\mu([0,2r])\,/\,\mu([r/2,3r/2])$", labelpad=2)
    panel_title(axb, "(b) doubling ratio")
    axc.set_xscale("log"); axc.set_yscale("log"); axc.set_xlim(10, 1e8); axc.set_ylim(0.4, 3e8)
    axc.set_xlabel(r"$r$"); axc.set_ylabel(r"$Q(r)=\mu([0,r])\,\nu([0,r])/r^2$", labelpad=2)
    panel_title(axc, r"(c) spherical $A_2$ ratio")
    fig.savefig(os.path.join(FIGDIR, "fig2_undecided.pdf"))
    fig.savefig(os.path.join(FIGDIR, "fig2_undecided.png"), dpi=220)
    plt.close(fig)

if __name__ == "__main__":
    fig1(); fig2()
    print("wrote fig1_geometries.pdf/.png and fig2_undecided.pdf/.png in", HERE)
