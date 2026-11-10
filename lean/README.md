# Lean proof development

Kernel-checked proofs for parts of `paper/radial-tests.tex`, with Lean
`v4.24.0` and Mathlib `v4.24.0` (pinned in `lean-toolchain` and
`lake-manifest.json`).

**The paper as a whole is not formalized.** What is and is not certified is
recorded result by result in [PAPER_STATUS.md](PAPER_STATUS.md); read that
file before quoting anything from this folder. The paper and arXiv sources
are unchanged.

## What is certified

Stated in `PaperTheorems.lean`, in the paper's vocabulary (parabolic means
zero capacity of the unit ball):

- `cor:cs`: the sphere test dominates the volume test.
- `thm:brown`(d), (e) as potential theory: sphere integral diverges implies
  parabolic; uniform ray condition implies not parabolic.
- `thm:A`: (iii) implies (ii) implies (i) with no hypothesis; the full
  equivalence with the one cited implication as an explicit hypothesis.
- `lem:a2`: bounded spherical A2 ratio makes the two radial tests exhaustive.
- `lem:lip`: Gaussian comparison, smooth marginal, bounded drift, transfer of
  capacity, doubling, Poincare constants and the ray condition.
- `lem:1d`: `mu([-r,r]) nu([-r,r]) <= 32 C D^3 r^2`.
- `thm:B`: the lattice construction and its regularity; (b) every ray
  integral diverges and the sphere integral converges, so both of Brown's
  tests are silent; (c) the volume grows like `r^3`; the separation of the
  circles.

Not certified: `thm:B`(a) (doubling and Poincare for the lattice weight),
everything statistical, and every cited theorem.

## Run

```powershell
cd lean
./check.ps1
```

`check.ps1` builds all modules, audits the transitive foundations of every
theorem (only `propext`, `Classical.choice`, `Quot.sound` are accepted), and
writes `verification.json` with source hashes. A fresh clone needs
`lake exe cache get` once to download the Mathlib build.

## Toolchain and editor

Lean is installed through elan at `%USERPROFILE%\.elan` (binaries in
`%USERPROFILE%\.elan\bin`). It is not on `PATH`; `check.ps1` finds it there.

The Lean project root is **this folder** (`lean/`), not the repository root.
An editor must open `lean/` itself as the project, because the Lean plugin
looks for `lean-toolchain` in the project root. Opening the repository root,
or attaching it to another PyCharm project, gives "Unable to locate lean
toolchain". VS Code with the `lean4` extension is the reference editor.

## Modules

| Module | Content |
|---|---|
| `BrownRadial`, `Analytic` | Scalar inequalities: dyadic series, reciprocal Cauchy--Schwarz, two-region variance |
| `Radial`, `Polar` | Dyadic integrability; polar integration; ball volume as primitive of spherical area; `cor:cs` |
| `Capacity`, `Comparability`, `Variance`, `WeightedBalls`, `Resistance` | Energy, capacity, variance, doubling, ball Poincare and ray condition under comparison of weights |
| `Gaussian`, `GaussianMarginal`, `MultivariateGaussian`, `GaussianSmooth` | `lem:lip`: standard normal law, marginal, comparison constants, smoothness, drift bound |
| `Rays`, `SphericalA2` | Bounded angular A2 ratio gives the uniform ray condition |
| `SphereTest` | Sphere test and volume test force zero capacity |
| `RayTest` | Ray test forces positive capacity |
| `OneDim` | `lem:1d`, quantitative claim |
| `LatticeRegularity`, `LatticeGeometry`, `LatticeSeparation` | The lattice weight, its log-Lipschitz bound, the circles, coverage, separation |
| `RayToll` | Every ray integral of the lattice weight diverges; ray test silent |
| `LatticeVolume` | Volume growth and sphere-mean lower bound of the lattice weight |
| `PaperTheorems` | Paper-facing statements assembled from the above |
| `Remainder` | Pointwise little-o need not integrate (context for `prop:noR`) |
| `Audit` | Foundation audit over all theorems |

Other files: [SOURCE_CHECKS.md](SOURCE_CHECKS.md) (reading of the cited
sources; not Lean proofs), [STATUS_AND_STRUCTURE.md](STATUS_AND_STRUCTURE.md)
(build snapshot and conventions), [HANDOFF_PROMPT.md](HANDOFF_PROMPT.md)
(instructions for continuing).
