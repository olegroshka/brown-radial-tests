import Capacity
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- Variance as minimization over the centering constant; for finite weighted
mass and square-integrable u the minimizer is the weighted mean. -/
noncomputable def weightedVariance (μ : Measure E) (w : E → ℝ≥0∞) (u : E → ℝ) : ℝ≥0∞ :=
  ⨅ m : ℝ, ∫⁻ x, ENNReal.ofReal ((u x-m)^2) * w x ∂μ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedVariance_upper (μ : Measure E) {w v : E → ℝ≥0∞}
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hhi : ∀ x, v x ≤ C*w x)
    (u : E → ℝ) : weightedVariance μ v u ≤ C * weightedVariance μ w u := by
  unfold weightedVariance
  rw [ENNReal.mul_iInf_of_ne hC0 hC]
  apply iInf_mono
  intro m
  rw [← lintegral_const_mul' C _ hC]
  apply lintegral_mono
  intro x
  simpa only [mul_left_comm] using mul_le_mul_left' (hhi x) (ENNReal.ofReal ((u x-m)^2))

/-- Transfer of the variational Poincare inequality under bounded comparison
of weights. This applies with μ restricted to any given ball. -/
theorem weighted_poincare_transfer (μ : Measure E) {w v : E → ℝ≥0∞}
    (tests : Set (E → ℝ))
    {c C P : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x)
    (hP : ∀ u ∈ tests, weightedVariance μ w u ≤ P * weightedEnergy μ w u) :
    ∀ u ∈ tests, weightedVariance μ v u ≤ (C*P/c) * weightedEnergy μ v u := by
  intro u hu
  have he := (weightedEnergy_comparison μ hc hC hlo hhi u).1
  have he' := mul_le_mul_left' he c⁻¹
  simp only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul] at he'
  calc
    weightedVariance μ v u ≤ C * weightedVariance μ w u := weightedVariance_upper μ hC0 hC hhi u
    _ ≤ C * (P * weightedEnergy μ w u) := mul_le_mul_left' (hP u hu) C
    _ ≤ C * (P * (c⁻¹ * weightedEnergy μ v u)) := mul_le_mul_left' (mul_le_mul_left' he' P) C
    _ = (C*P/c) * weightedEnergy μ v u := by simp only [div_eq_mul_inv, mul_assoc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Measure comparison on every measurable set. -/
theorem weighted_measure_comparison (μ : Measure E) {w v : E → ℝ≥0∞}
    {c C : ℝ≥0∞} (hc : c ≠ ⊤) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x)
    {A : Set E} (hA : MeasurableSet A) :
    c * μ.withDensity w A ≤ μ.withDensity v A ∧
      μ.withDensity v A ≤ C * μ.withDensity w A := by
  rw [withDensity_apply w hA, withDensity_apply v hA,
    ← lintegral_const_mul' c _ hc, ← lintegral_const_mul' C _ hC]
  exact ⟨lintegral_mono hlo, lintegral_mono hhi⟩

omit [NormedSpace ℝ E] in
/-- Doubling transfers, with its constant explicitly tracked. -/
theorem weighted_doubling_transfer [BorelSpace E] (μ : Measure E) {w v : E → ℝ≥0∞}
    {c C D : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x)
    (hD : ∀ x r, 0 < r → μ.withDensity w (Metric.ball x (2*r)) ≤ D * μ.withDensity w (Metric.ball x r)) :
    ∀ x r, 0 < r → μ.withDensity v (Metric.ball x (2*r)) ≤ (C*D/c) * μ.withDensity v (Metric.ball x r) := by
  intro x r hr
  have hsmall := (weighted_measure_comparison μ hc hC hlo hhi (A := Metric.ball x r) measurableSet_ball).1
  have hsmall' := mul_le_mul_left' hsmall c⁻¹
  simp only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul] at hsmall'
  calc
    μ.withDensity v (Metric.ball x (2*r)) ≤ C * μ.withDensity w (Metric.ball x (2*r)) :=
      (weighted_measure_comparison μ hc hC hlo hhi measurableSet_ball).2
    _ ≤ C * (D * μ.withDensity w (Metric.ball x r)) := mul_le_mul_left' (hD x r hr) C
    _ ≤ C * (D * (c⁻¹ * μ.withDensity v (Metric.ball x r))) := mul_le_mul_left' (mul_le_mul_left' hsmall' D) C
    _ = (C*D/c) * μ.withDensity v (Metric.ball x r) := by simp only [div_eq_mul_inv, mul_assoc]

end BrownRadial
