import Variance
import Gaussian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Set Metric
open scoped NNReal ENNReal ContDiff
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- Continuous densities have finite mass on every bounded ball. -/
theorem weighted_ball_finite {w : E → ℝ} (hw : Continuous w) (a : E) (r : ℝ) :
    IsFiniteMeasure ((μ.restrict (ball a r)).withDensity (fun x => ENNReal.ofReal (w x))) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact ((hw.continuousOn.integrableOn_compact (isCompact_closedBall a r)).mono_set
    ball_subset_closedBall).hasFiniteIntegral

/-- Continuity on the closed ball discharges the weighted moment hypotheses;
no regularity or measurability outside that ball is needed. -/
theorem continuousOn_weighted_ball_integrable {w u : E → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 ≤ w x) {a : E} {r : ℝ} (hu : ContinuousOn u (closedBall a r)) :
    Integrable u ((μ.restrict (ball a r)).withDensity (fun x => ENNReal.ofReal (w x))) := by
  apply (integrable_withDensity_iff_integrable_smul'
    hw.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
  exact (((hw.continuousOn.mul hu).integrableOn_compact
    (isCompact_closedBall a r)).mono_set ball_subset_closedBall)

/-- The variational variance is the actual weighted-mean variance on each
ball for every function continuous on its closure, including all C1 tests. -/
theorem weightedVariance_ball_eq_mean {w u : E → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 ≤ w x) {a : E} {r : ℝ} (hu : ContinuousOn u (closedBall a r)) :
    weightedVariance (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u =
      ENNReal.ofReal (∫ x, (u x - ⨍ y, u y
        ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r))^2
        ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r)) := by
  rw [restrict_withDensity measurableSet_ball]
  haveI := weighted_ball_finite μ hw a r
  exact weightedVariance_eq_mean_ae _ hw.measurable.ennreal_ofReal.aemeasurable
    (continuousOn_weighted_ball_integrable μ hw hp hu)
    (continuousOn_weighted_ball_integrable μ hw hp (hu.pow 2))

/-- The paper's C1-on-the-closed-ball test class, stated using ambient
functions. Their values outside the ball play no part in its integrals. -/
def ballC1Tests (a : E) (r : ℝ) : Set (E → ℝ) :=
  {u | ContDiffOn ℝ 1 u (closedBall a r)}

/-- Poincare comparison on the actual C1 ball test class, centered at each
weight's own mean. The energy uses the ambient derivative norm; on real
Hilbert spaces `weightedEnergy_eq_gradient` identifies it with gradient energy. -/
theorem weighted_ball_poincare_transfer {w v : E → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ x, 0 ≤ v x)
    {c C P : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hlo : ∀ x, c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (hhi : ∀ x, ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (a : E) (r : ℝ)
    (hP : ∀ u ∈ ballC1Tests a r,
      ENNReal.ofReal (∫ x, (u x - ⨍ y, u y
        ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r))^2
        ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r)) ≤
      P * weightedEnergy (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u) :
    ∀ u ∈ ballC1Tests a r,
      ENNReal.ofReal (∫ x, (u x - ⨍ y, u y
        ∂(μ.withDensity (fun z => ENNReal.ofReal (v z))).restrict (ball a r))^2
        ∂(μ.withDensity (fun z => ENNReal.ofReal (v z))).restrict (ball a r)) ≤
      (C * P / c) * weightedEnergy (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (v x)) u := by
  have hvar : ∀ u ∈ ballC1Tests a r,
      weightedVariance (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u ≤
        P * weightedEnergy (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u := by
    intro u hu
    rw [weightedVariance_ball_eq_mean μ hw hw0 hu.continuousOn]
    exact hP u hu
  intro u hu
  rw [← weightedVariance_ball_eq_mean μ hv hv0 hu.continuousOn]
  exact weighted_poincare_transfer (μ.restrict (ball a r)) (ballC1Tests a r)
    hc0 hc hC0 hC hlo hhi hvar u hu

/-- Scale-invariant Poincare inequality with the paper's own weighted mean,
same-ball energy, and C1 test class. Constants are extended nonnegative reals;
applications below require them to be finite. -/
def ballPoincare (w : E → ℝ) (P : ℝ≥0∞) : Prop :=
  ∀ a r, 0 < r → ∀ u ∈ ballC1Tests a r,
    ENNReal.ofReal (∫ x, (u x - ⨍ y, u y
      ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r))^2
      ∂(μ.withDensity (fun z => ENNReal.ofReal (w z))).restrict (ball a r)) ≤
    (P * ENNReal.ofReal (r^2)) *
      weightedEnergy (μ.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u

theorem ballPoincare_transfer {w v : E → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ x, 0 ≤ v x)
    {c C P : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hlo : ∀ x, c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (v x))
    (hhi : ∀ x, ENNReal.ofReal (v x) ≤ C * ENNReal.ofReal (w x))
    (hP : ballPoincare μ w P) : ballPoincare μ v (C * P / c) := by
  intro a r hr u hu
  have h := weighted_ball_poincare_transfer μ hw hv hw0 hv0 hc0 hc hC0 hC hlo hhi
    a r (hP a r hr) u hu
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Existence of a finite, uniform all-ball Poincare constant is preserved by
Gaussian averaging of a positive log-Lipschitz weight. This uses actual ball
means and needs no differentiability assumption on the original weight. -/
theorem gaussian_ballPoincare_iff (γ : Measure E) [ProbabilityTheory.IsGaussian γ]
    {w : E → ℝ} {L : ℝ≥0} (hp : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ballPoincare μ w P) ↔
      ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ballPoincare μ (gaussianAverage γ w) P := by
  have hw := continuous_of_lipschitz_log hp hlog
  have hvp := gaussianAverage_pos γ hp hlog
  have hv := continuous_of_lipschitz_log hvp (gaussianAverage_log_lipschitz γ hp hlog)
  obtain ⟨c, C, hc0, hc, hC0, hC, hlo, hhi⟩ := gaussian_comparable_ennreal γ hp hlog
  constructor
  · rintro ⟨P, hPfin, hP⟩
    refine ⟨C * P / c, ENNReal.div_ne_top (ENNReal.mul_ne_top hC hPfin) hc0, ?_⟩
    exact ballPoincare_transfer μ hw hv (fun x => (hp x).le) (fun x => (hvp x).le)
      hc0 hc hC0 hC hlo hhi hP
  · rintro ⟨P, hPfin, hP⟩
    have hlo' (x : E) : C⁻¹ * ENNReal.ofReal (gaussianAverage γ w x) ≤ ENNReal.ofReal (w x) := by
      have h := mul_le_mul_left' (hhi x) C⁻¹
      simpa only [← mul_assoc, ENNReal.inv_mul_cancel hC0 hC, one_mul] using h
    have hhi' (x : E) : ENNReal.ofReal (w x) ≤ c⁻¹ * ENNReal.ofReal (gaussianAverage γ w x) := by
      have h := mul_le_mul_left' (hlo x) c⁻¹
      simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul] using h
    refine ⟨c⁻¹ * P / C⁻¹,
      ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) hPfin)
        (ENNReal.inv_ne_zero.mpr hC), ?_⟩
    exact ballPoincare_transfer μ hv hw (fun x => (hvp x).le) (fun x => (hp x).le)
      (ENNReal.inv_ne_zero.mpr hC) (ENNReal.inv_ne_top.mpr hC0)
      (ENNReal.inv_ne_zero.mpr hc) (ENNReal.inv_ne_top.mpr hc0) hlo' hhi' hP

end BrownRadial
