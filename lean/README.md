# Lean verification

Kernel-checked proofs for parts of `paper/radial-tests.tex`, in Lean
`v4.24.0` with Mathlib `v4.24.0` (pinned in `lean-toolchain` and
`lake-manifest.json`).

**The paper as a whole is not formalized.** Its main theorems rest on
published theorems that exist in no Lean library. Those enter only as named
hypotheses of clearly labelled statements; nothing is added to the logical
foundations. Every theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## Run

```powershell
cd lean
./check.ps1
```

`check.ps1` builds all modules, audits the foundations of every theorem and
writes `verification.json` (status, counts, source hashes, the hash of the
paper). A fresh clone needs `lake exe cache get` once. Lean is found on
`PATH` or in `%USERPROFILE%\.elan\bin`. Open `lean/` itself as the editor
project: the toolchain file is here, not in the repository root.

## What is certified

"Parabolic" means zero capacity of the unit ball for smooth compactly
supported tests. All weights are continuous and positive.

| Result of the paper | Status | Main Lean statement |
|---|---|---|
| `cor:cs` | proved | `sphere_volume_corollary` |
| `thm:brown` (d), (e), as potential theory | proved | `sphere_test_capacity_zero`, `ray_test_capacity_pos` |
| `lem:lip` | proved | `Gaussian*`, `Comparability`, `WeightedBalls` |
| `thm:volume`, "integral diverges implies parabolic" | proved | `volume_test_capacity_zero` |
| `thm:A` | proved modulo the cited direction of `thm:volume` | `theorem_A_modulo_volume_criterion` |
| `lem:a2` | proved | `lemma_a2` |
| `lem:1d`, first claim | proved | `one_dimensional_doubling_poincare_A2` |
| `lem:glue` | proved | `gluing_lemma_of_local_doubling`, `gluing_lemma` |
| `lem:circle` | proved modulo three premises | `circle_lemma_final` |
| `thm:B` construction, (b), (c) | proved | `theorem_B_tests_silent`, `theorem_B_volume_growth` |
| `thm:B` (a), every `alpha >= 0` | proved modulo three premises | `theorem_B_a_final` |
| `thm:B` conclusion, `alpha >= 4` | proved modulo four premises | `theorem_B_final`, `theorem_B_statement_final` |

Not formalized: `thm:cyl`, `lem:thomson`, `prop:wall`, `prop:log`,
`prop:komaki`, `prop:noR`, the second half of `lem:1d`, and everything
statistical (Brown's Theorem 5.1.1).

## The premises

Hypotheses of the final statements in `ThmBFinal.lean`; none is proved here.

| Premise | Says | Source |
|---|---|---|
| `RadialPoincarePremise alpha` | `(1 + \|x - c\|^2)^(alpha/2)` satisfies the Poincare inequality on all balls, uniformly in `c` | Bjorn 2001, Prop. 6, with Hajlasz--Koskela; or Grigor'yan--Saloff-Coste 2005, Prop. 4.9 |
| `SelfImprovementUniformPremise` | doubling and a Poincare inequality with energy over `4B` on all balls give the inequality with energy over `B`, with a constant depending only on the two constants | Hajlasz--Koskela 2000, Thm 5.1 and Cor. 9.8 |
| `CircleNearPoincarePremise alpha` | the Poincare inequality for the weight of one circle at small balls near the circle | the paper's own argument (proof of `lem:circle`); checked by hand, **not a published theorem** |
| `VolumeCriterionPremise` | for a doubling--Poincare weight, parabolic implies that the volume integral diverges | Sturm 1996, Cor. 4.11 and 4.12, with Fukushima--Oshima--Takeda |

The doubling halves of the first and third premise are theorems
(`radial_weight_doublingAll`, `circle_near_doubling`).

## Modules

One flat folder, one library per file; `Audit.lean` imports everything.

| Group | Modules |
|---|---|
| Scalar and radial tools | `BrownRadial`, `Analytic`, `Radial`, `Polar` |
| Capacity, variance, comparison of weights | `Capacity`, `Comparability`, `Variance`, `WeightedBalls`, `Resistance` |
| Gaussian marginal (`lem:lip`) | `Gaussian`, `GaussianMarginal`, `MultivariateGaussian`, `GaussianSmooth` |
| Brown's tests | `Rays`, `SphericalA2`, `SphereTest`, `RayTest`, `OneDim` |
| The lattice weight: construction, (b), (c) | `LatticeRegularity`, `LatticeGeometry`, `LatticeSeparation`, `RayToll`, `LatticeVolume`, `PaperTheorems` |
| Doubling and Poincare: vocabulary, `lem:glue` | `DoublingPoincare`, `CubePartition`, `Gluing`, `LebesguePoincare` |
| `thm:B` (a) | `LatticeLocal`, `LatticeSmallBalls`, `LatticeCovering`, `LatticeDP` |
| `lem:circle` | `CircleLocal`, `CubeGrid`, `CircleLemma` |
| Final statements | `ThmBFinal` |
| Other | `Remainder` (context for `prop:noR`), `Audit` |

## Conventions

All declarations are in the namespace `BrownRadial`, declared with `theorem`
under plain ASCII names; `check.ps1` relies on this. Infinite quantities
live in `ENNReal`. Line numbers quoted in docstrings refer to the paper at
commit `36e9c61`. Do not run `lake update`.
