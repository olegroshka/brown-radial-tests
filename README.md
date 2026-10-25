# Beyond Brown's radial tests

Reproducible materials for the paper

> O. Roshka, *Beyond Brown's radial tests: admissibility, parabolicity, and a
> doubling–Poincaré prior that neither test decides* (2026).

Brown (1971) proved that a generalized Bayes estimator of a normal mean is
admissible exactly when a diffusion attached to the prior is recurrent, and gave
two radial tests that can both fall silent. Reading his criterion as the
potential theory of a weighted Euclidean space, this note asks what the modern
geometry of recurrence (doubling measures, Poincaré inequalities, heat-kernel and
volume tests) adds inside that undecided zone. The main result is an explicit
doubling–Poincaré prior on **R³** whose generalized Bayes estimator is
inadmissible although neither of Brown's radial tests decides it.

## Layout

```
paper/          LaTeX source (radial-tests.tex), bibliography, and the compiled PDF
figures/        the two computed figures used in the paper (PDF + PNG)
code/           Python scripts that reproduce the numbers of Section 6
code/results/   saved output of those scripts (the runs of record)
```

## Build the paper

```
cd paper
pdflatex radial-tests.tex
pdflatex radial-tests.tex
```

The bibliography is inlined in `radial-tests.tex`, so no BibTeX pass is needed;
`references.bib` is kept for provenance.

## Reproduce the numbers

The scripts need NumPy, SciPy, and Matplotlib. Run them from `code/`.

| script | what it computes |
|---|---|
| `scattered_weight.py` | the lattice prior (Thm 4.1): ray and sphere integrals, volume growth, doubling, Lipschitz constant |
| `poincare_eigen.py` | Poincaré constants as weighted Neumann eigenvalues on axis-centred balls (Table 3) |
| `offaxis_eigen3d.py` | the full three-dimensional off-axis eigenvalues (Table 3) |
| `ring_weight.py` | the coherent "wall" (Prop 5.2): flux terms and the two-region quotient |
| `radial_tests.py` | Brown's two tests and the volume test on the product weight; the one-dimensional heat kernel (Prop 5.3) |
| `one_dim_weights.py` | doubling ratios and spherical A₂ ratios of one-dimensional weights (Lemma 3.3) |
| `make_fig_undecided.py` | regenerates `figures/fig2_undecided.*` |
| `make_fig_lattice_wall.py` | regenerates `figures/fig3_lattice_vs_wall.*` |

Saved outputs of record are in `code/results/`.

## Author and license

Oleg Roshka · ORCID [0009-0009-3075-9417](https://orcid.org/0009-0009-3075-9417) · oleg.roshka@proton.me

The paper text and figures are released under **CC BY 4.0**; the code is under the
**MIT License** (see `LICENSE`).
