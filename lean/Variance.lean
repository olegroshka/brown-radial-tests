import Comparability
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory
open scoped ENNReal
namespace BrownRadial

variable {X : Type*} [MeasurableSpace X]

theorem integrable_centered_square (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x)^2) μ)
    (m : ℝ) : Integrable (fun x => (u x-m)^2) μ := by
  have h := (hu2.sub (hu.const_mul (2*m))).add (integrable_const (m^2))
  convert h using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The centering identity with the actual mean of an arbitrary finite measure.
It includes the zero measure and does not assume probability normalization. -/
theorem centered_square_identity (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x)^2) μ)
    (m : ℝ) :
    (∫ x, (u x-m)^2 ∂μ) = (∫ x, (u x-⨍ y, u y ∂μ)^2 ∂μ) +
      μ.real Set.univ * ((⨍ y, u y ∂μ)-m)^2 := by
  let a := ⨍ y, u y ∂μ
  have hc : Integrable (fun x => u x-a) μ := hu.sub (integrable_const a)
  have hs := integrable_centered_square μ hu hu2 a
  have hid : (fun x => (u x-m)^2) =
      (fun x => (u x-a)^2 + (2*(a-m))*(u x-a) + (a-m)^2) := by
    ext x
    ring
  rw [hid, integral_add (f := fun x => (u x-a)^2 + (2*(a-m))*(u x-a))
      (hs.add (hc.const_mul _)) (integrable_const _),
    integral_add hs (hc.const_mul _), integral_const_mul]
  have hz : (∫ x, u x-a ∂μ) = 0 := integral_sub_average μ u
  rw [hz, mul_zero, add_zero, integral_const, smul_eq_mul]

theorem mean_minimizes_square (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x)^2) μ)
    (m : ℝ) :
    (∫ x, (u x-⨍ y, u y ∂μ)^2 ∂μ) ≤ ∫ x, (u x-m)^2 ∂μ := by
  rw [centered_square_identity μ hu hu2 m]
  exact le_add_of_nonneg_right (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

/-- The variational definition used for comparison is exactly the weighted
mean variance appearing in the paper's Poincare inequality. -/
theorem weightedVariance_eq_mean_ae (μ : Measure X) {w : X → ℝ≥0∞} {u : X → ℝ}
    (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)]
    (hi : Integrable u (μ.withDensity w))
    (hi2 : Integrable (fun x => (u x)^2) (μ.withDensity w)) :
    weightedVariance μ w u =
      ENNReal.ofReal (∫ x, (u x-⨍ y, u y ∂μ.withDensity w)^2 ∂μ.withDensity w) := by
  have hid (m : ℝ) : (∫⁻ x, ENNReal.ofReal ((u x-m)^2)*w x ∂μ) =
      ENNReal.ofReal (∫ x, (u x-m)^2 ∂μ.withDensity w) := by
    have hi' := integrable_centered_square _ hi hi2 m
    rw [ofReal_integral_eq_lintegral_ofReal hi'
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
      lintegral_withDensity_eq_lintegral_mul₀' hw hi'.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    simp only [Pi.mul_apply, mul_comm]
  unfold weightedVariance
  simp_rw [hid]
  exact le_antisymm (iInf_le _ _) (le_iInf fun m =>
    ENNReal.ofReal_le_ofReal (mean_minimizes_square _ hi hi2 m))

/-- Measurable-function interface retained for the existing callers. -/
theorem weightedVariance_eq_mean (μ : Measure X) {w : X → ℝ≥0∞} {u : X → ℝ}
    (hw : Measurable w) (hu : Measurable u) [IsFiniteMeasure (μ.withDensity w)]
    (hi : Integrable u (μ.withDensity w))
    (hi2 : Integrable (fun x => (u x)^2) (μ.withDensity w)) :
    weightedVariance μ w u =
      ENNReal.ofReal (∫ x, (u x-⨍ y, u y ∂μ.withDensity w)^2 ∂μ.withDensity w) := by
  have hid (m : ℝ) : (∫⁻ x, ENNReal.ofReal ((u x-m)^2)*w x ∂μ) =
      ENNReal.ofReal (∫ x, (u x-m)^2 ∂μ.withDensity w) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_centered_square _ hi hi2 m)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
      lintegral_withDensity_eq_lintegral_mul μ hw (by fun_prop)]
    simp only [Pi.mul_apply, mul_comm]
  unfold weightedVariance
  simp_rw [hid]
  apply le_antisymm
  · exact iInf_le _ _
  · exact le_iInf (fun m => ENNReal.ofReal_le_ofReal (mean_minimizes_square _ hi hi2 m))

end BrownRadial
