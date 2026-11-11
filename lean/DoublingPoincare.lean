import WeightedBalls
import LatticeGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Vocabulary for the proof of `thm:B`(a): doubling and the Poincare inequality
at one ball, their transfer under comparison of weights on that ball only,
and the cited inputs of the series as `Prop`-valued definitions.

Nothing here proves a cited result. `LebesguePoincarePremise`,
`SelfImprovementPremise` and `CircleLemmaPremise` are statements; they occur
later only as named hypotheses.
-/

open MeasureTheory Set Metric Module
open scoped NNReal ENNReal ContDiff
namespace BrownRadial

/-! ### Comparison of densities on one measurable set -/

section OnSet

variable {X : Type*} [MeasurableSpace X]

/-- Upper comparison of weighted masses when the densities are compared on
the set only. -/
theorem withDensity_le_of_le_on (μ : Measure X) {s : Set X} (hs : MeasurableSet s)
    {w v : X → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤) (hhi : ∀ x ∈ s, v x ≤ C * w x) :
    μ.withDensity v s ≤ C * μ.withDensity w s := by
  rw [withDensity_apply _ hs, withDensity_apply _ hs, ← lintegral_const_mul' C _ hC]
  exact setLIntegral_mono' hs hhi

/-- Lower comparison of weighted masses when the densities are compared on
the set only. No finiteness of the constant is needed. -/
theorem withDensity_ge_of_ge_on (μ : Measure X) {s : Set X} (hs : MeasurableSet s)
    {w v : X → ℝ≥0∞} {c : ℝ≥0∞} (hlo : ∀ x ∈ s, c * w x ≤ v x) :
    c * μ.withDensity w s ≤ μ.withDensity v s := by
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact (lintegral_const_mul_le c _).trans (setLIntegral_mono' hs hlo)

end OnSet

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- Doubling at one ball. -/
def doublingAt (μ : Measure E) (w : E → ℝ) (D : ℝ≥0∞) (a : E) (r : ℝ) : Prop :=
  μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a (2 * r)) ≤
    D * μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a r)

/-- Doubling at every ball of positive radius, with one constant. -/
def doublingAll (μ : Measure E) (w : E → ℝ) (D : ℝ≥0∞) : Prop :=
  ∀ a r, 0 < r → doublingAt μ w D a r

/-- Poincare at one ball, energy over the `lam`-fold ball. `lam = 1` is the
inequality `(eq:poincare)` of the paper; `lam = 4` is the weak form produced
by the gluing lemma. Tests are C1 on the closed `lam`-fold ball. The left side
is the variational variance, which equals the variance about the weighted
mean for continuous nonnegative weights (`poincareAt_iff_mean`). -/
def poincareAt (μ : Measure E) (w : E → ℝ) (P : ℝ≥0∞) (lam : ℝ) (a : E) (r : ℝ) : Prop :=
  ∀ u : E → ℝ, ContDiffOn ℝ 1 u (closedBall a (lam * r)) →
    weightedVariance (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u ≤
      (P * ENNReal.ofReal (r ^ 2)) *
        weightedEnergy (μ.restrict (ball a (lam * r))) (fun x => ENNReal.ofReal (w x)) u

/-! ### Inclusions of concentric balls, valid for every sign of the radius -/

omit [NormedSpace ℝ E] [MeasurableSpace E] in
theorem ball_subset_ball_scaled (a : E) (r : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) :
    ball a r ⊆ ball a (lam * r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.mpr hr]
    exact empty_subset _
  · exact ball_subset_ball (by nlinarith)

omit [NormedSpace ℝ E] [MeasurableSpace E] in
theorem closedBall_subset_closedBall_scaled (a : E) (r : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) :
    closedBall a r ⊆ closedBall a (lam * r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [closedBall_eq_empty.mpr hr]
    exact empty_subset _
  · exact closedBall_subset_closedBall (by nlinarith)

/-! ### Monotonicity and degenerate radii -/

omit [NormedSpace ℝ E] in
theorem doublingAt_mono {μ : Measure E} {w : E → ℝ} {D D' : ℝ≥0∞} (hD : D ≤ D')
    {a : E} {r : ℝ} (h : doublingAt μ w D a r) : doublingAt μ w D' a r :=
  h.trans (mul_le_mul_right' hD _)

omit [NormedSpace ℝ E] in
theorem doublingAll_mono {μ : Measure E} {w : E → ℝ} {D D' : ℝ≥0∞} (hD : D ≤ D')
    (h : doublingAll μ w D) : doublingAll μ w D' :=
  fun a r hr => doublingAt_mono hD (h a r hr)

omit [NormedSpace ℝ E] in
/-- A ball of nonpositive radius is empty, so doubling there is vacuous. -/
theorem doublingAt_of_nonpos (μ : Measure E) (w : E → ℝ) (D : ℝ≥0∞) (a : E) {r : ℝ}
    (hr : r ≤ 0) : doublingAt μ w D a r := by
  unfold doublingAt
  rw [ball_eq_empty.mpr (by linarith : 2 * r ≤ 0), measure_empty]
  exact zero_le _

omit [NormedSpace ℝ E] in
/-- Iterated doubling: the `2^n`-fold ball. -/
theorem doublingAll_iterate {μ : Measure E} {w : E → ℝ} {D : ℝ≥0∞} (h : doublingAll μ w D)
    (a : E) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a (2 ^ n * r)) ≤
      D ^ n * μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (2:ℝ) ^ (n + 1) * r = 2 * (2 ^ n * r) := by ring
    rw [h2, pow_succ, mul_comm (D ^ n) D, mul_assoc]
    exact (h a (2 ^ n * r) (by positivity)).trans (mul_le_mul_left' ih D)

theorem poincareAt_mono {μ : Measure E} {w : E → ℝ} {P P' : ℝ≥0∞} (hP : P ≤ P')
    {lam : ℝ} {a : E} {r : ℝ} (h : poincareAt μ w P lam a r) : poincareAt μ w P' lam a r :=
  fun u hu => (h u hu).trans (mul_le_mul_right' (mul_le_mul_right' hP _) _)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The variational variance against the zero measure vanishes. -/
theorem weightedVariance_zero_measure (w : E → ℝ≥0∞) (u : E → ℝ) :
    weightedVariance (0 : Measure E) w u = 0 := by
  unfold weightedVariance
  simp

/-- On a ball of nonpositive radius the left side vanishes, so the Poincare
inequality is vacuous there. -/
theorem poincareAt_of_nonpos (μ : Measure E) (w : E → ℝ) (P : ℝ≥0∞) (lam : ℝ) (a : E)
    {r : ℝ} (hr : r ≤ 0) : poincareAt μ w P lam a r := by
  intro u _
  rw [ball_eq_empty.mpr hr, Measure.restrict_empty, weightedVariance_zero_measure]
  exact zero_le _

/-- A larger energy domain and a smaller test class: the inequality with
dilation `lam` implies the inequality with any larger dilation. -/
theorem poincareAt_mono_dilation {μ : Measure E} {w : E → ℝ} {P : ℝ≥0∞} {lam lam' : ℝ}
    (hl : lam ≤ lam') {a : E} {r : ℝ} (h : poincareAt μ w P lam a r) :
    poincareAt μ w P lam' a r := by
  rcases le_or_gt r 0 with hr | hr
  · exact poincareAt_of_nonpos μ w P lam' a hr
  · intro u hu
    have hle : lam * r ≤ lam' * r := mul_le_mul_of_nonneg_right hl hr.le
    refine (h u (hu.mono (closedBall_subset_closedBall hle))).trans ?_
    unfold weightedEnergy
    exact mul_le_mul_left' (lintegral_mono_set (ball_subset_ball hle)) _

/-- The strong inequality (energy over the ball itself) implies every weak
form (energy over the `lam`-fold ball, `lam ≥ 1`). -/
theorem poincareAt_weak_of_strong {μ : Measure E} {w : E → ℝ} {P : ℝ≥0∞} {lam : ℝ}
    (hl : 1 ≤ lam) {a : E} {r : ℝ} (h : poincareAt μ w P 1 a r) :
    poincareAt μ w P lam a r :=
  poincareAt_mono_dilation hl h

/-! ### Comparison of weights on the ball only -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Upper comparison of the variational variance on a measurable set, the
densities being compared on that set only. -/
theorem weightedVariance_le_of_le_on (μ : Measure E) {s : Set E} (hs : MeasurableSet s)
    {w v : E → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤) (hhi : ∀ x ∈ s, v x ≤ C * w x) (u : E → ℝ) :
    weightedVariance (μ.restrict s) v u ≤ C * weightedVariance (μ.restrict s) w u := by
  unfold weightedVariance
  rw [ENNReal.mul_iInf (fun h => absurd h hC)]
  apply iInf_mono
  intro m
  rw [← lintegral_const_mul' C _ hC]
  apply setLIntegral_mono' hs
  intro x hx
  simpa only [mul_left_comm] using mul_le_mul_left' (hhi x hx) (ENNReal.ofReal ((u x - m) ^ 2))

/-- Lower comparison of the energy on a measurable set, the densities being
compared on that set only. -/
theorem weightedEnergy_ge_of_ge_on (μ : Measure E) {s : Set E} (hs : MeasurableSet s)
    {w v : E → ℝ≥0∞} {c : ℝ≥0∞} (hlo : ∀ x ∈ s, c * w x ≤ v x) (u : E → ℝ) :
    c * weightedEnergy (μ.restrict s) w u ≤ weightedEnergy (μ.restrict s) v u := by
  unfold weightedEnergy
  refine (lintegral_const_mul_le c _).trans ?_
  apply setLIntegral_mono' hs
  intro x hx
  simpa only [mul_left_comm] using
    mul_le_mul_left' (hlo x hx) (ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2))

variable [BorelSpace E]

/-- Local transfer of the Poincare inequality, sharpest form. The upper
comparison is needed on the ball (left side), the lower comparison on the
`lam`-fold ball (energy). No restriction on `lam`. -/
theorem poincareAt_transfer_split {μ : Measure E} {w v : E → ℝ} {c C P : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC : C ≠ ⊤) {lam : ℝ} {a : E} {r : ℝ}
    (hhi : ∀ x ∈ ball a r, ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (hlo : ∀ x ∈ ball a (lam * r), c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (h : poincareAt μ w P lam a r) : poincareAt μ v (C * P / c) lam a r := by
  intro u hu
  have he := weightedEnergy_ge_of_ge_on μ (measurableSet_ball (x := a) (ε := lam * r)) hlo u
  have he' := mul_le_mul_left' he c⁻¹
  simp only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul] at he'
  calc
    weightedVariance (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (v x)) u
        ≤ C * weightedVariance (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u :=
          weightedVariance_le_of_le_on μ measurableSet_ball hC hhi u
    _ ≤ C * ((P * ENNReal.ofReal (r ^ 2)) *
          weightedEnergy (μ.restrict (ball a (lam * r))) (fun x => ENNReal.ofReal (w x)) u) :=
          mul_le_mul_left' (h u hu) C
    _ ≤ C * ((P * ENNReal.ofReal (r ^ 2)) * (c⁻¹ *
          weightedEnergy (μ.restrict (ball a (lam * r))) (fun x => ENNReal.ofReal (v x)) u)) :=
          mul_le_mul_left' (mul_le_mul_left' he' _) C
    _ = (C * P / c * ENNReal.ofReal (r ^ 2)) *
          weightedEnergy (μ.restrict (ball a (lam * r))) (fun x => ENNReal.ofReal (v x)) u := by
          rw [div_eq_mul_inv]
          ring

/-- Local transfer of the Poincare inequality: the comparison of the weights
is assumed on `ball a (lam * r)` only, `lam ≥ 1`. -/
theorem poincareAt_transfer_local {μ : Measure E} {w v : E → ℝ} {c C P : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC : C ≠ ⊤) {lam : ℝ} (hlam : 1 ≤ lam) {a : E} {r : ℝ}
    (hlo : ∀ x ∈ ball a (lam * r), c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (hhi : ∀ x ∈ ball a (lam * r), ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (h : poincareAt μ w P lam a r) : poincareAt μ v (C * P / c) lam a r :=
  poincareAt_transfer_split hc0 hc hC
    (fun x hx => hhi x (ball_subset_ball_scaled a r hlam hx)) hlo h

/-- The same with real constants: `c * w ≤ v ≤ C * w` on `ball a (lam * r)`. -/
theorem poincareAt_transfer_local_real {μ : Measure E} {w v : E → ℝ} {c C : ℝ} {P : ℝ≥0∞}
    (hc : 0 < c) (hC : 0 ≤ C) {lam : ℝ} (hlam : 1 ≤ lam) {a : E} {r : ℝ}
    (hcmp : ∀ x ∈ ball a (lam * r), c * w x ≤ v x ∧ v x ≤ C * w x)
    (h : poincareAt μ w P lam a r) :
    poincareAt μ v (ENNReal.ofReal C * P / ENNReal.ofReal c) lam a r := by
  refine poincareAt_transfer_local (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hlam ?_ ?_ h
  · intro x hx
    rw [← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (hcmp x hx).1
  · intro x hx
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (hcmp x hx).2

/-- Multiplying the weight by a positive constant does not change the
Poincare constant. -/
theorem poincareAt_const_mul {μ : Measure E} {w : E → ℝ} {P : ℝ≥0∞} {s : ℝ} (hs : 0 < s)
    {lam : ℝ} {a : E} {r : ℝ} (h : poincareAt μ w P lam a r) :
    poincareAt μ (fun x => s * w x) P lam a r := by
  have h0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hkey := poincareAt_transfer_split (v := fun x => s * w x) (c := ENNReal.ofReal s)
    (C := ENNReal.ofReal s) h0 ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (fun x _ => (ENNReal.ofReal_mul hs.le).le) (fun x _ => (ENNReal.ofReal_mul hs.le).ge) h
  have hconst : ENNReal.ofReal s * P / ENNReal.ofReal s = P := by
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right h0 ENNReal.ofReal_ne_top
  rwa [hconst] at hkey

/-- Multiplying the weight by a positive constant: equivalence. -/
theorem poincareAt_const_mul_iff {μ : Measure E} {w : E → ℝ} {P : ℝ≥0∞} {s : ℝ} (hs : 0 < s)
    {lam : ℝ} {a : E} {r : ℝ} :
    poincareAt μ (fun x => s * w x) P lam a r ↔ poincareAt μ w P lam a r := by
  refine ⟨fun h => ?_, poincareAt_const_mul hs⟩
  have h' := poincareAt_const_mul (inv_pos.mpr hs) h
  have he : (fun x => s⁻¹ * (s * w x)) = w := by
    funext x
    field_simp
  rwa [he] at h'

omit [NormedSpace ℝ E] in
/-- Local transfer of doubling, sharpest form: the lower comparison is needed
on the ball, the upper comparison on the doubled ball. -/
theorem doublingAt_transfer_split {μ : Measure E} {w v : E → ℝ} {c C D : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC : C ≠ ⊤) {a : E} {r : ℝ}
    (hlo : ∀ x ∈ ball a r, c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (hhi : ∀ x ∈ ball a (2 * r), ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (h : doublingAt μ w D a r) : doublingAt μ v (C * D / c) a r := by
  unfold doublingAt at h ⊢
  have hsmall := withDensity_ge_of_ge_on μ (measurableSet_ball (x := a) (ε := r)) hlo
  have hsmall' := mul_le_mul_left' hsmall c⁻¹
  simp only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul] at hsmall'
  calc
    μ.withDensity (fun x => ENNReal.ofReal (v x)) (ball a (2 * r))
        ≤ C * μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a (2 * r)) :=
          withDensity_le_of_le_on μ measurableSet_ball hC hhi
    _ ≤ C * (D * μ.withDensity (fun x => ENNReal.ofReal (w x)) (ball a r)) :=
          mul_le_mul_left' h C
    _ ≤ C * (D * (c⁻¹ * μ.withDensity (fun x => ENNReal.ofReal (v x)) (ball a r))) :=
          mul_le_mul_left' (mul_le_mul_left' hsmall' D) C
    _ = (C * D / c) * μ.withDensity (fun x => ENNReal.ofReal (v x)) (ball a r) := by
          simp only [div_eq_mul_inv, mul_assoc]

omit [NormedSpace ℝ E] in
/-- Local transfer of doubling: the comparison of the weights is assumed on
`ball a (2 * r)` only. -/
theorem doublingAt_transfer_local {μ : Measure E} {w v : E → ℝ} {c C D : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC : C ≠ ⊤) {a : E} {r : ℝ}
    (hlo : ∀ x ∈ ball a (2 * r), c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (hhi : ∀ x ∈ ball a (2 * r), ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (h : doublingAt μ w D a r) : doublingAt μ v (C * D / c) a r :=
  doublingAt_transfer_split hc0 hc hC
    (fun x hx => hlo x (ball_subset_ball_scaled a r one_le_two hx)) hhi h

omit [NormedSpace ℝ E] in
/-- The same with real constants: `c * w ≤ v ≤ C * w` on `ball a (2 * r)`. -/
theorem doublingAt_transfer_local_real {μ : Measure E} {w v : E → ℝ} {c C : ℝ} {D : ℝ≥0∞}
    (hc : 0 < c) (hC : 0 ≤ C) {a : E} {r : ℝ}
    (hcmp : ∀ x ∈ ball a (2 * r), c * w x ≤ v x ∧ v x ≤ C * w x)
    (h : doublingAt μ w D a r) :
    doublingAt μ v (ENNReal.ofReal C * D / ENNReal.ofReal c) a r := by
  refine doublingAt_transfer_local (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top ?_ ?_ h
  · intro x hx
    rw [← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (hcmp x hx).1
  · intro x hx
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (hcmp x hx).2

omit [NormedSpace ℝ E] in
/-- Multiplying the weight by a positive constant does not change the
doubling constant. -/
theorem doublingAt_const_mul {μ : Measure E} {w : E → ℝ} {D : ℝ≥0∞} {s : ℝ} (hs : 0 < s)
    {a : E} {r : ℝ} (h : doublingAt μ w D a r) :
    doublingAt μ (fun x => s * w x) D a r := by
  have h0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hkey := doublingAt_transfer_split (v := fun x => s * w x) (c := ENNReal.ofReal s)
    (C := ENNReal.ofReal s) h0 ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (fun x _ => (ENNReal.ofReal_mul hs.le).ge) (fun x _ => (ENNReal.ofReal_mul hs.le).le) h
  have hconst : ENNReal.ofReal s * D / ENNReal.ofReal s = D := by
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right h0 ENNReal.ofReal_ne_top
  rwa [hconst] at hkey

/-! ### A weight bounded above and below on a ball is as good as the constant weight -/

/-- Poincare for a weight with `w ≤ M` on the ball and `m ≤ w` on the
`lam`-fold ball, from Poincare for the constant weight. -/
theorem poincareAt_of_bounds_split {μ : Measure E} {w : E → ℝ} {m M : ℝ} (hm : 0 < m)
    {P : ℝ≥0∞} {lam : ℝ} {a : E} {r : ℝ}
    (hhi : ∀ x ∈ ball a r, w x ≤ M) (hlo : ∀ x ∈ ball a (lam * r), m ≤ w x)
    (h : poincareAt μ (fun _ => 1) P lam a r) :
    poincareAt μ w (ENNReal.ofReal (M / m) * P) lam a r := by
  have hkey := poincareAt_transfer_split (v := w) (c := ENNReal.ofReal m)
    (C := ENNReal.ofReal M) (ENNReal.ofReal_pos.mpr hm).ne' ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top
    (fun x hx => by
      rw [ENNReal.ofReal_one, mul_one]
      exact ENNReal.ofReal_le_ofReal (hhi x hx))
    (fun x hx => by
      rw [ENNReal.ofReal_one, mul_one]
      exact ENNReal.ofReal_le_ofReal (hlo x hx)) h
  have hconst : ENNReal.ofReal M * P / ENNReal.ofReal m = ENNReal.ofReal (M / m) * P := by
    rw [ENNReal.ofReal_div_of_pos hm, ENNReal.mul_div_right_comm]
  rwa [hconst] at hkey

/-- If `m ≤ w ≤ M` on `ball a (lam * r)` with `0 < m` and `lam ≥ 1`, Poincare
for the constant weight gives Poincare for `w` with constant `(M / m) * P`. -/
theorem poincareAt_of_bounds {μ : Measure E} {w : E → ℝ} {m M : ℝ} (hm : 0 < m)
    {P : ℝ≥0∞} {lam : ℝ} (hlam : 1 ≤ lam) {a : E} {r : ℝ}
    (hb : ∀ x ∈ ball a (lam * r), m ≤ w x ∧ w x ≤ M)
    (h : poincareAt μ (fun _ => 1) P lam a r) :
    poincareAt μ w (ENNReal.ofReal (M / m) * P) lam a r :=
  poincareAt_of_bounds_split hm
    (fun x hx => (hb x (ball_subset_ball_scaled a r hlam hx)).2) (fun x hx => (hb x hx).1) h

end Basic

/-! ### Haar measure: doubling with constant `2 ^ finrank` -/

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Scaling of Haar measure on balls, for every real radius. -/
theorem haar_ball_two_mul (a : E) (r : ℝ) :
    μ (ball a (2 * r)) = 2 ^ finrank ℝ E * μ (ball a r) := by
  rw [Measure.addHaar_ball_mul_of_pos μ a two_pos r, Measure.addHaar_ball_center μ a r,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- Lebesgue (Haar) measure is doubling with constant `2 ^ finrank`. -/
theorem lebesgue_doublingAll : doublingAll μ (fun _ => 1) (2 ^ finrank ℝ E) := by
  intro a r _
  unfold doublingAt
  simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
  exact (haar_ball_two_mul μ a r).le

/-- If `w ≤ M` on the doubled ball and `0 < m ≤ w` on the ball, the weight is
doubling at that ball with constant `(M / m) * 2 ^ finrank`. -/
theorem doublingAt_of_bounds {w : E → ℝ} {m M : ℝ} (hm : 0 < m) {a : E} {r : ℝ}
    (hhi : ∀ x ∈ ball a (2 * r), w x ≤ M) (hlo : ∀ x ∈ ball a r, m ≤ w x) :
    doublingAt μ w (ENNReal.ofReal (M / m) * 2 ^ finrank ℝ E) a r := by
  have hbase : doublingAt μ (fun _ => 1) (2 ^ finrank ℝ E) a r := by
    unfold doublingAt
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul]
    exact (haar_ball_two_mul μ a r).le
  have hkey := doublingAt_transfer_split (v := w) (c := ENNReal.ofReal m)
    (C := ENNReal.ofReal M) (ENNReal.ofReal_pos.mpr hm).ne' ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top
    (fun x hx => by
      rw [ENNReal.ofReal_one, mul_one]
      exact ENNReal.ofReal_le_ofReal (hlo x hx))
    (fun x hx => by
      rw [ENNReal.ofReal_one, mul_one]
      exact ENNReal.ofReal_le_ofReal (hhi x hx)) hbase
  have hconst : ENNReal.ofReal M * 2 ^ finrank ℝ E / ENNReal.ofReal m =
      ENNReal.ofReal (M / m) * 2 ^ finrank ℝ E := by
    rw [ENNReal.ofReal_div_of_pos hm, ENNReal.mul_div_right_comm]
  rwa [hconst] at hkey

end Haar

/-! ### Variance about the weighted mean -/

section Mean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- For a continuous nonnegative weight and `lam ≥ 1`, `poincareAt` is the
inequality of the paper: the left side is the integral of the squared
deviation from the weighted mean over the ball. -/
theorem poincareAt_iff_mean {w : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (P : ℝ≥0∞) {lam : ℝ} (hlam : 1 ≤ lam) (a : E) (r : ℝ) :
    poincareAt μ w P lam a r ↔
      ∀ u : E → ℝ, ContDiffOn ℝ 1 u (closedBall a (lam * r)) →
        ENNReal.ofReal (∫ x, (u x - ⨍ y, u y
          ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r)) ^ 2
          ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r)) ≤
        (P * ENNReal.ofReal (r ^ 2)) *
          weightedEnergy (μ.restrict (ball a (lam * r))) (fun x => ENNReal.ofReal (w x)) u := by
  have hcont : ∀ u : E → ℝ, ContDiffOn ℝ 1 u (closedBall a (lam * r)) →
      ContinuousOn u (closedBall a r) :=
    fun u hu => hu.continuousOn.mono (closedBall_subset_closedBall_scaled a r hlam)
  constructor
  · intro h u hu
    rw [← weightedVariance_ball_eq_mean μ hw hw0 (hcont u hu)]
    exact h u hu
  · intro h u hu
    rw [weightedVariance_ball_eq_mean μ hw hw0 (hcont u hu)]
    exact h u hu

/-- `poincareAt` with `lam = 1` at all balls is the existing `ballPoincare`,
for continuous nonnegative weights. -/
theorem poincareAt_one_iff_ballPoincare {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (P : ℝ≥0∞) :
    (∀ a r, 0 < r → poincareAt μ w P 1 a r) ↔ ballPoincare μ w P := by
  constructor
  · intro h a r hr u hu
    have hu' : ContDiffOn ℝ 1 u (closedBall a (1 * r)) := by rwa [one_mul]
    have h' := (poincareAt_iff_mean μ hw hw0 P le_rfl a r).mp (h a r hr) u hu'
    rwa [one_mul] at h'
  · intro h a r hr
    refine (poincareAt_iff_mean μ hw hw0 P le_rfl a r).mpr ?_
    intro u hu
    rw [one_mul] at hu ⊢
    exact h a r hr u hu

end Mean

/-! ### The premises of the series -/

/-- P0. Lebesgue measure on three-space satisfies the scale-invariant
Poincare inequality on every ball, energy over the ball itself, tests C1 on
the closed ball. Classical; a statement only. -/
def LebesguePoincarePremise : Prop :=
  ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
    poincareAt (volume : Measure (EuclideanSpace ℝ (Fin 3))) (fun _ => 1) P 1 a r

/-- P3. Weak Poincare (energy over the 4-fold ball, tests C1 on the closed
4-fold ball) at every ball, together with doubling at every ball, gives the
strong inequality at every ball, for continuous positive weights on
three-space. Cited from Hajlasz and Koskela; a statement only. -/
def SelfImprovementPremise : Prop :=
  ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, Continuous w → (∀ x, 0 < w x) →
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure (EuclideanSpace ℝ (Fin 3))) w D) →
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
      poincareAt (volume : Measure (EuclideanSpace ℝ (Fin 3))) w P 4 a r) →
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
      poincareAt (volume : Measure (EuclideanSpace ℝ (Fin 3))) w P 1 a r

/-- The weight of `lem:circle`. -/
noncomputable def circleWeight (C : Set LatticeSpace) (alpha : ℝ) (x : LatticeSpace) : ℝ :=
  (1 + Metric.infDist x C ^ 2) ^ (alpha / 2)

/-- `lem:circle` for the circles of the lattice, with constants uniform in
the circle. A statement only. -/
def CircleLemmaPremise (alpha : ℝ) : Prop :=
  ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
    ∀ (k : ℕ), 4 ≤ k → ∀ (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k)),
      doublingAll (volume : Measure LatticeSpace)
          (circleWeight (indexedLatticeCircle k i j) alpha) D ∧
        ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (indexedLatticeCircle k i j) alpha) P 1 a r

theorem circleWeight_pos (C : Set LatticeSpace) (alpha : ℝ) (x : LatticeSpace) :
    0 < circleWeight C alpha x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem circleWeight_continuous (C : Set LatticeSpace) (alpha : ℝ) :
    Continuous (circleWeight C alpha) := by
  unfold circleWeight
  exact (continuous_const.add ((continuous_infDist_pt C).pow 2)).rpow_const
    (fun x => Or.inl (by positivity : (1 + infDist x C ^ 2) ≠ 0))

/-- For a nonnegative exponent the circle weight is at least one. -/
theorem one_le_circleWeight (C : Set LatticeSpace) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (x : LatticeSpace) : 1 ≤ circleWeight C alpha x :=
  Real.one_le_rpow (by nlinarith [sq_nonneg (infDist x C)]) (by positivity)

/-! ### Three-space -/

/-- Lebesgue measure on three-space is doubling with constant 8. -/
theorem lebesgue_doublingAll_three :
    doublingAll (volume : Measure LatticeSpace) (fun _ => 1) 8 := by
  have h := lebesgue_doublingAll (volume : Measure LatticeSpace)
  rw [finrank_euclideanSpace_fin] at h
  norm_num at h
  exact h

/-- Three-space: `w ≤ M` on the doubled ball and `0 < m ≤ w` on the ball give
doubling at that ball with constant `8 M / m`. -/
theorem doublingAt_of_bounds_three {w : LatticeSpace → ℝ} {m M : ℝ} (hm : 0 < m)
    {a : LatticeSpace} {r : ℝ}
    (hhi : ∀ x ∈ ball a (2 * r), w x ≤ M) (hlo : ∀ x ∈ ball a r, m ≤ w x) :
    doublingAt (volume : Measure LatticeSpace) w (ENNReal.ofReal (M / m) * 8) a r := by
  have h := doublingAt_of_bounds (volume : Measure LatticeSpace) hm hhi hlo
  rw [finrank_euclideanSpace_fin] at h
  norm_num at h
  exact h

/-- P0 with a weight that is bounded above and below on the ball: the strong
Poincare inequality at that ball with constant `(M / m) * P`, where `P` is the
Lebesgue constant. -/
theorem poincareAt_of_lebesgue_premise (hleb : LebesguePoincarePremise) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (w : LatticeSpace → ℝ) (m M : ℝ) (a : LatticeSpace) (r : ℝ),
      0 < m → 0 < r → (∀ x ∈ ball a r, m ≤ w x ∧ w x ≤ M) →
      poincareAt (volume : Measure LatticeSpace) w (ENNReal.ofReal (M / m) * P) 1 a r := by
  obtain ⟨P, hP, h⟩ := hleb
  refine ⟨P, hP, fun w m M a r hm hr hb => ?_⟩
  refine poincareAt_of_bounds hm le_rfl ?_ (h a r hr)
  intro x hx
  rw [one_mul] at hx
  exact hb x hx

end BrownRadial
