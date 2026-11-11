import Gluing
import LatticeSmallBalls
import LatticeCovering
import PaperTheorems

/-!
`thm:B`(a) modulo the premises of the series: the lattice weight is doubling
and satisfies the scale-invariant Poincare inequality on all balls.

* Large balls, `rho >= sigma_0 / 10` (paper, paragraph "Large balls"): the
  gluing lemma `gluing_lemma` is applied with `nu` Lebesgue measure and the
  covering of `LatticeCovering`, with the paper's numbers: cubes of side
  `l_j = sigma(y_j) / 32`, enlargement `1.01`, neighbouring sides within
  `1.03`, balls `B_j = B(y_j, 2.7 l_j)`. (G1) is the cell mass of
  `LatticeLocal`; the Poincare half of (G2) is `lattice_small_ball_poincare`
  on `B_j`; the mass comparison `mu(B_j) <= K mu(Q_j)` goes through Lebesgue
  measure and the cell mass; the Poincare inequality of `nu` at `2B` is
  `LebesguePoincarePremise`. The result is the weak inequality, energy over
  `4B`.
* Doubling at large balls is the mass bound of `LatticeLocal`; no premise.
* All balls: small or large, by the radius against `sigma_0 / 10`.
* `SelfImprovementPremise` turns doubling and the weak inequality at all
  balls into the strong inequality.

The unproved inputs are the named hypotheses `LebesguePoincarePremise`,
`CircleLemmaPremise alpha`, `SelfImprovementPremise` and, in the last
statements only, `VolumeCriterionPremise`. Part (a) is proved for every
`alpha >= 0`; `alpha >= 4` enters only through parts (b), (c).
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### Mass comparisons for the cells of the covering -/

/-- From `c * a <= b` with `c > 0`: `a <= (1 / c) * b`. -/
theorem lattice_dp_le_of_mul_le {c : ℝ} (hc : 0 < c) {a b : ℝ≥0∞}
    (h : ENNReal.ofReal c * a ≤ b) : a ≤ ENNReal.ofReal (1 / c) * b := by
  calc a = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * a) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / c) * b := mul_le_mul_left' h _

/-- (G1), lower half, for the cells of the covering: `|Q| <= (1 / c) mu(Q)`
for the cube of side `sigma(y) / 32` centred at `y`, with the constant of
`lattice_cell_mass_cube` at `M = 64`. Every centre, including those in
`{|x| < 16}`. -/
theorem lattice_dp_cell_mass {α : ℝ} (hα : 0 ≤ α) (y : LatticeSpace) :
    volume (cube y (Real.sqrt (1 + ‖y‖) / 32)) ≤
      ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(α/2) / 1536 / 8)) *
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (cube y (Real.sqrt (1 + ‖y‖) / 32)) := by
  have h := (lattice_cell_mass_cube hα (M := 64) (by norm_num) y
    (l := Real.sqrt (1 + ‖y‖) / 32) (le_of_eq (by ring))).1
  exact lattice_dp_le_of_mul_le (by positivity) h

/-- The mass comparison of (G2) for the cells of the covering:
`mu(B_j) <= |B_j| = 5.4^3 |B(y_j, l_j / 2)| <= 5.4^3 |Q_j| <= K mu(Q_j)`. -/
theorem lattice_dp_ball_le_cube {α : ℝ} (hα : 0 ≤ α) (y : LatticeSpace) :
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball y (27 / 10 * (Real.sqrt (1 + ‖y‖) / 32))) ≤
      ENNReal.ofReal ((27 / 5 : ℝ) ^ 3) *
        ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(α/2) / 1536 / 8)) *
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (cube y (Real.sqrt (1 + ‖y‖) / 32)) := by
  have h1 := lattice_mass_le_volume hα (ball y (27 / 10 * (Real.sqrt (1 + ‖y‖) / 32)))
  have h2 := lattice_mass_ball_scale y y (c := 27 / 5) (by norm_num) (Real.sqrt (1 + ‖y‖) / 64)
  have h3 : ball y (Real.sqrt (1 + ‖y‖) / 64) ⊆ cube y (Real.sqrt (1 + ‖y‖) / 32) := by
    have h := cube_closedBall_subset y (Real.sqrt (1 + ‖y‖) / 32)
    rw [show Real.sqrt (1 + ‖y‖) / 32 / 2 = Real.sqrt (1 + ‖y‖) / 64 by ring] at h
    exact ball_subset_closedBall.trans h
  have h4 := lattice_dp_cell_mass hα y
  rw [show 27 / 10 * (Real.sqrt (1 + ‖y‖) / 32) = 27 / 5 * (Real.sqrt (1 + ‖y‖) / 64) by ring]
    at h1 ⊢
  calc _ ≤ volume (ball y (27 / 5 * (Real.sqrt (1 + ‖y‖) / 64))) := h1
    _ = ENNReal.ofReal ((27 / 5 : ℝ) ^ 3) * volume (ball y (Real.sqrt (1 + ‖y‖) / 64)) := h2
    _ ≤ ENNReal.ofReal ((27 / 5 : ℝ) ^ 3) * volume (cube y (Real.sqrt (1 + ‖y‖) / 32)) :=
        mul_le_mul_left' (measure_mono h3) _
    _ ≤ ENNReal.ofReal ((27 / 5 : ℝ) ^ 3) *
          (ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(α/2) / 1536 / 8)) *
          (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
            (cube y (Real.sqrt (1 + ‖y‖) / 32))) := mul_le_mul_left' h4 _
    _ = _ := by rw [mul_assoc]

/-- Paper: the sides `l_j = sigma(y_j) / 32` of cells centred in shell
`k >= 4` lie in the range `[s_k / 32, s_k]` of the cell-mass paragraph; in
fact `l_j <= 0.045 s_k`. (The Lean cell mass is stated through `sigma` and
does not need this.) -/
theorem lattice_dp_cell_side_range {k : ℕ} (hk : 4 ≤ k) {y : LatticeSpace}
    (h1 : (2:ℝ)^k ≤ ‖y‖) (h2 : ‖y‖ < (2:ℝ)^(k+1)) :
    Real.sqrt ((2:ℝ)^k) / 32 ≤ Real.sqrt (1 + ‖y‖) / 32 ∧
      Real.sqrt (1 + ‖y‖) / 32 ≤ 45 / 1000 * Real.sqrt ((2:ℝ)^k) := by
  have ha := lattice_local_sigma_ge h1
  have hb := lattice_local_sigma_le hk h2
  constructor <;> linarith

/-! ### Large balls -/

/-- **Large balls, weak Poincare.** Modulo the Poincare inequality of
Lebesgue measure and `lem:circle`: the lattice weight satisfies the Poincare
inequality with energy over the 4-fold ball at every ball of radius at least
`sigma(x_0) / 10`, with one constant. The centre is arbitrary; nothing but
`sigma_0 <= 10 rho` is used. -/
theorem lattice_large_ball_weak_poincare {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ),
      Real.sqrt (1 + ‖x0‖) / 10 ≤ rho →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        K 4 x0 rho := by
  obtain ⟨P, hP, hsmall⟩ := lattice_small_ball_poincare halpha hleb hcircle
  obtain ⟨Pν, hPν, hν⟩ := hleb
  obtain ⟨K, hK, hglue⟩ := gluing_lemma.{0} 3 (κ := 101 / 100) (by norm_num) 13824 2176782
    (103 / 100) (27 / 10)
    (G := max 1 (ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(alpha/2) / 1536 / 8))))
    (P := P)
    (Kb := ENNReal.ofReal ((27 / 5 : ℝ) ^ 3) *
      ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(alpha/2) / 1536 / 8)))
    (Pν := Pν)
    (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top).ne hP
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hPν
  refine ⟨K, hK, fun x0 rho hρ => ?_⟩
  obtain ⟨u, hfin, hs, hcov, hN0, hdiam, hΛ, hball, hin, hNb, hR⟩ :=
    lattice_covering_gluing_hypotheses x0 hρ
  haveI : Fintype u := hfin.fintype
  have h0 := lattice_covering_sigma_one_le x0
  refine hglue u (fun y => (y : LatticeSpace))
    (fun y => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) (fun y => (y : LatticeSpace))
    (fun y => 27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32))
    (latticeWeight latticeValleys alpha) (fun _ => 1) x0 rho
    (latticeWeight_continuous _ _) (fun x => (latticeWeight_pos _ _ x).le) continuous_const
    hs hcov hN0 hdiam hΛ hball (fun y => le_rfl) hin hNb ?_ ?_
    (fun y => hsmall y _ (hR y).1 (hR y).2)
    (fun y => lattice_dp_ball_le_cube halpha y) (hν x0 (2 * rho) (by linarith))
  · intro y
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
    exact (lattice_mass_le_volume halpha _).trans (le_mul_of_one_le_left' (le_max_left _ _))
  · intro y
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
    exact (lattice_dp_cell_mass halpha y).trans (mul_le_mul_right' (le_max_right _ _) _)

/-- **Large balls, weak Poincare, with (G2) as `lem:glue` states it.** The
same conclusion from `gluing_lemma_of_local_doubling`: the second half of
(G2) is doubling at every ball centred in `B_j` with radius at most that of
`B_j`. Such balls are small balls, so this is `lattice_small_ball_doubling`.
This is the form in which the paper invokes the lemma ("(G2) holds on it by
the previous paragraph"). -/
theorem lattice_large_ball_weak_poincare_local_doubling {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ),
      Real.sqrt (1 + ‖x0‖) / 10 ≤ rho →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        K 4 x0 rho := by
  obtain ⟨P, hP, hsmall⟩ := lattice_small_ball_poincare halpha hleb hcircle
  obtain ⟨D, hD, hsmallD⟩ := lattice_small_ball_doubling halpha hcircle
  obtain ⟨Pν, hPν, hν⟩ := hleb
  obtain ⟨K, hK, hglue⟩ := gluing_lemma_of_local_doubling.{0} 3 (κ := 101 / 100) (by norm_num)
    13824 2176782 (103 / 100) (27 / 10)
    (G := max 1 (ENNReal.ofReal (1 / ((1 / (21600 * (64:ℝ)^2 + 1))^(alpha/2) / 1536 / 8))))
    (P := P) (D := D) (Pν := Pν)
    (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top).ne hP hD hPν
  refine ⟨K, hK, fun x0 rho hρ => ?_⟩
  obtain ⟨u, hfin, hs, hcov, hN0, hdiam, hΛ, hball, hin, hNb, hR⟩ :=
    lattice_covering_gluing_hypotheses x0 hρ
  haveI : Fintype u := hfin.fintype
  have h0 := lattice_covering_sigma_one_le x0
  refine hglue u (fun y => (y : LatticeSpace))
    (fun y => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) (fun y => (y : LatticeSpace))
    (fun y => 27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32))
    (latticeWeight latticeValleys alpha) (fun _ => 1) x0 rho
    (latticeWeight_continuous _ _) (fun x => (latticeWeight_pos _ _ x).le) continuous_const
    hs hcov hN0 hdiam hΛ hball (fun y => le_rfl) hin hNb ?_ ?_
    (fun y => hsmall y _ (hR y).1 (hR y).2)
    (fun y a ha r hr0 hr => hsmallD a r hr0 (lattice_covering_ball_inner_small ha hr))
    (hν x0 (2 * rho) (by linarith))
  · intro y
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
    exact (lattice_mass_le_volume halpha _).trans (le_mul_of_one_le_left' (le_max_left _ _))
  · intro y
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
    exact (lattice_dp_cell_mass halpha y).trans (mul_le_mul_right' (le_max_right _ _) _)

/-- Paper: "balls of radius `> 8` centred in `{|x| < 16}` are covered by the
large-ball argument, which uses only `sigma_0 < 10 rho`". -/
theorem lattice_large_ball_weak_poincare_near_origin {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ), ‖x0‖ < 16 → 8 < rho →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        K 4 x0 rho := by
  obtain ⟨K, hK, h⟩ := lattice_large_ball_weak_poincare halpha hleb hcircle
  exact ⟨K, hK, fun x0 rho hx0 hρ =>
    h x0 rho (by linarith [lattice_local_large_radius_near_origin hx0 hρ])⟩

/-- **Large balls, doubling.** `mu(2B) <= |2B| = 8 |B| <= (8 / c) mu(B)` at
every ball of radius at least `sigma(x_0) / 10`. No premise. -/
theorem lattice_large_ball_doubling {alpha : ℝ} (halpha : 0 ≤ alpha) (x0 : LatticeSpace)
    {rho : ℝ} (hrho : Real.sqrt (1 + ‖x0‖) / 10 ≤ rho) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
      (ENNReal.ofReal (8 / ((1 / (21600 * (10:ℝ)^2 + 1))^(alpha/2) / 1536))) x0 rho :=
  lattice_mass_double_ball halpha (by norm_num) x0 hrho

/-- Paper: "doubling of `mu` at scales at least `sigma / 32`". The mass bound
gives it from `sigma_0 / 32` up, so the range overlaps that of the small
balls, `rho <= sigma_0 / 10`. No premise. -/
theorem lattice_cell_scale_doubling {alpha : ℝ} (halpha : 0 ≤ alpha) (x0 : LatticeSpace)
    {rho : ℝ} (hrho : Real.sqrt (1 + ‖x0‖) / 32 ≤ rho) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
      (ENNReal.ofReal (8 / ((1 / (21600 * (32:ℝ)^2 + 1))^(alpha/2) / 1536))) x0 rho :=
  lattice_mass_double_ball halpha (by norm_num) x0 hrho

/-! ### All balls -/

/-- **Doubling at all balls**, modulo `lem:circle` (used for small balls
only). Every ball is small (`rho <= sigma_0 / 10`) or large
(`rho >= sigma_0 / 10`). -/
theorem lattice_doubling_all {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D := by
  obtain ⟨Ds, hDs, hs⟩ := lattice_small_ball_doubling halpha hcircle
  refine ⟨max Ds (ENNReal.ofReal (8 / ((1 / (21600 * (10:ℝ)^2 + 1))^(alpha/2) / 1536))),
    (max_lt hDs.lt_top ENNReal.ofReal_lt_top).ne, fun a r hr => ?_⟩
  rcases le_total r (Real.sqrt (1 + ‖a‖) / 10) with h | h
  · exact doublingAt_mono (le_max_left _ _) (hs a r hr h)
  · exact doublingAt_mono (le_max_right _ _) (lattice_large_ball_doubling halpha a h)

/-- **Weak Poincare at all balls**, energy over the 4-fold ball, modulo the
Poincare inequality of Lebesgue measure and `lem:circle`. Small balls: the
strong inequality implies the weak one. Large balls: the gluing lemma. -/
theorem lattice_weak_poincare_all {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 4 a r := by
  obtain ⟨Ps, hPs, hs⟩ := lattice_small_ball_poincare halpha hleb hcircle
  obtain ⟨K, hK, hl⟩ := lattice_large_ball_weak_poincare halpha hleb hcircle
  refine ⟨max Ps K, (max_lt hPs.lt_top hK.lt_top).ne, fun a r hr => ?_⟩
  rcases le_total r (Real.sqrt (1 + ‖a‖) / 10) with h | h
  · exact poincareAt_mono (le_max_left _ _)
      (poincareAt_weak_of_strong (by norm_num) (hs a r hr h))
  · exact poincareAt_mono (le_max_right _ _) (hl a r h)

/-! ### Theorem B(a) -/

/-- **`thm:B`(a) modulo the premises.** For every `alpha >= 0` the lattice
weight is doubling on all balls and satisfies the scale-invariant Poincare
inequality `(eq:poincare)` on all balls, given the Poincare inequality of
Lebesgue measure, `lem:circle` for the lattice circles, and the
self-improvement of the weak inequality. -/
theorem theorem_B_a_modulo_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 a r) :=
  ⟨lattice_doubling_all halpha hcircle,
    hself _ (latticeWeight_continuous _ _) (latticeWeight_pos _ _)
      (lattice_doubling_all halpha hcircle) (lattice_weak_poincare_all halpha hleb hcircle)⟩

/-- `thm:B`(a) modulo the premises, with the Poincare inequality in the form
`ballPoincare`: variance about the weighted mean, energy over the ball, tests
C1 on the closed ball. -/
theorem theorem_B_a_ball_poincare_modulo_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ballPoincare (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) P) := by
  obtain ⟨hD, P, hP, h⟩ := theorem_B_a_modulo_premises halpha hleb hcircle hself
  exact ⟨hD, P, hP, (poincareAt_one_iff_ballPoincare volume (latticeWeight_continuous _ _)
    (fun x => (latticeWeight_pos _ _ x).le) P).mp h⟩

/-! ### The conclusion of Theorem B -/

/-- P1: the cited direction of `thm:volume`, for continuous positive weights
on three-space: a doubling and Poincare weight that is parabolic has a
divergent volume integral. A statement only; it is used as a named hypothesis
of the theorems below. -/
def VolumeCriterionPremise : Prop :=
  ∀ w : LatticeSpace → ℝ, Continuous w → (∀ x, 0 < w x) →
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧ doublingAll (volume : Measure LatticeSpace) w D) →
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) w P 1 a r) →
    parabolic (volume : Measure LatticeSpace) w →
    volumeTestFires (volume : Measure LatticeSpace) w

/-- **`thm:B`, conclusion, modulo the four premises**: for `alpha >= 4` the
lattice weight and its Gaussian marginal are not parabolic. -/
theorem theorem_B_modulo_premises {alpha : ℝ≥0} (halpha : 4 ≤ (alpha : ℝ))
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) (hvol : VolumeCriterionPremise) :
    ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
    ¬ parabolic (volume : Measure LatticeSpace)
      (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha)) := by
  have h0 : (0 : ℝ) ≤ alpha := by linarith
  obtain ⟨hD, hP⟩ := theorem_B_a_modulo_premises h0 hleb hcircle hself
  exact theorem_B_not_parabolic_modulo_volume_criterion halpha
    (hvol _ (latticeWeight_continuous _ _) (latticeWeight_pos _ _) hD hP)

/-- **`thm:B`, all parts, modulo the four premises**, for `alpha >= 4`:
(a) doubling and Poincare on all balls; (b) the sphere test, the ray test and
the volume test are silent; (c) the volume of balls grows like `r^3`; and the
weight and its Gaussian marginal are not parabolic. Parts (b) and (c) use no
premise. -/
theorem theorem_B_statement_modulo_premises {alpha : ℝ≥0} (halpha : 4 ≤ (alpha : ℝ))
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) (hvol : VolumeCriterionPremise) :
    ((∃ D : ℝ≥0∞, D ≠ ⊤ ∧
        doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
      (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
        poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
          P 1 a r)) ∧
    (¬ sphereTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ rayTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ volumeTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 64 ≤ r →
      c * r^3 ≤ weightedBallVolume volume (latticeWeight latticeValleys alpha) r ∧
      weightedBallVolume volume (latticeWeight latticeValleys alpha) r ≤
        (4/3) * Real.pi * r^3) ∧
    (¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ parabolic (volume : Measure LatticeSpace)
        (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha))) := by
  have h0 : (0 : ℝ) ≤ alpha := by linarith
  exact ⟨theorem_B_a_modulo_premises h0 hleb hcircle hself, theorem_B_tests_silent halpha,
    theorem_B_volume_growth h0, theorem_B_modulo_premises halpha hleb hcircle hself hvol⟩

end BrownRadial
