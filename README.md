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
companion/      a self-contained HTML reader's guide to the paper
arxiv/          flattened copy for an arXiv upload (the .tex + the two figure PDFs in one folder)
```

## Build the paper

```
cd paper
pdflatex radial-tests.tex
pdflatex radial-tests.tex
```

The bibliography is inlined in `radial-tests.tex`, so no BibTeX pass is needed;
`references.bib` is kept for provenance.

## Uploading to arXiv

arXiv compiles from the top level of the uploaded archive and will not follow a
`../` path outside it, so the `paper/` + `figures/` split cannot be uploaded as
is (the two figures come back as "missing from the source"). The `arxiv/` folder
is a flattened copy for exactly this: `radial-tests.tex` and both figure PDFs in a
single directory, with `\graphicspath` pointing at `./`. Zip its *contents* -- the
files must sit at the archive's top level, not inside a subfolder:

```
cd arxiv
zip ../radial-tests-arxiv.zip radial-tests.tex fig2_undecided.pdf fig3_lattice_vs_wall.pdf
```

No BibTeX pass or `.bbl` is needed; arXiv runs pdflatex itself.

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
| `companion_bench.py` | the numbers of the companion guide's test bench (Section 15): Brown's two tests, the ball probe and the true resistance on the lattice and wall priors |

Saved outputs of record are in `code/results/`.

## Companion

`companion/explainer.html` is a self-contained reader's guide to the paper at the
level of a first mathematics degree, written for statisticians, geometers and
physicists, and people who build models. It opens with the whole story on one
page and three reading routes, and each Part starts with its idea in plain words.
It builds up the background (priors and Gaussian blur, random walks, weighted
spaces, the electrical reading of recurrence), explains step by step what Brown's
two radial tests compute, runs both tests and the ball probe side by side on the
paper's two priors (a test bench, with the true resistance for comparison), states
the results, and adds a Part on where the
microstructure matters in practice (expected-return shrinkage, Langevin samplers,
regime priors), with each link labelled by how firm it is. Live demos, computed in
the browser: the resistance sandwich (an exact network solve with Brown's two
bounds), a probe that tells walls from threads, a sampler on regime priors, and
the test bench, where Brown's instruments and the probe run on the paper's priors.
Open it in a web browser.

## Author and license

Oleg Roshka · ORCID [0009-0009-3075-9417](https://orcid.org/0009-0009-3075-9417) · oleg.roshka@proton.me

The paper text and figures are released under **CC BY 4.0**; the code is under the
**MIT License** (see `LICENSE`).
