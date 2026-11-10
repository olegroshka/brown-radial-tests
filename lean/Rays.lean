import BrownRadial
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Prod
import Resistance

open MeasureTheory
open scoped ENNReal
namespace BrownRadial

/-- Analytic core of `lem:a2`: an integrable upper bound on the angular mean
of a nonnegative kernel yields a positive-measure set of directions whose
entire ray integrals have a common finite bound. Extended integrals retain
infinite ray resistances instead of totalizing them to zero. -/
theorem angular_mean_bound_gives_uniform_rays
    {R D : Type*} [MeasurableSpace R] [MeasurableSpace D]
    (μ : Measure R) (ν : Measure D) [SFinite μ] [IsProbabilityMeasure ν]
    {k : R → D → ℝ≥0∞} {b : R → ℝ≥0∞} {C : ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) (hb : Measurable b)
    (hC : C ≠ ∞) (hbfinite : (∫⁻ r, b r ∂μ) ≠ ∞)
    (hmean : ∀ r, (∫⁻ d, k r d ∂ν) ≤ C * b r) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      0 < ν {d | (∫⁻ r, k r d ∂μ) ≤ M} := by
  let M := ∫⁻ d, ∫⁻ r, k r d ∂μ ∂ν
  have hfinite : M ≠ ∞ := by
    have hle : M ≤ C * (∫⁻ r, b r ∂μ) := by
      dsimp [M]
      rw [← lintegral_lintegral_swap hk.aemeasurable]
      exact (lintegral_mono hmean).trans_eq (lintegral_const_mul C hb)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hbfinite) hle
  exact ⟨M, hfinite, measure_le_lintegral_pos hk.lintegral_prod_left.aemeasurable⟩

/-- Bounded angular A2 ratio makes the ray test fire whenever the sphere
resistance is finite. With R = [1,infinity), D the unit sphere, and
q(r) = r^(dimension-1), these are the actual two radial-test kernels. -/
theorem bounded_angular_A2_gives_uniformRayTest
    {R D : Type*} [MeasurableSpace R] [MeasurableSpace D]
    (μ : Measure R) (ν : Measure D) [SFinite μ] [IsProbabilityMeasure ν]
    {w : R → D → ℝ≥0∞} {q : R → ℝ≥0∞} {C : ℝ≥0∞}
    (hw : Measurable (Function.uncurry w)) (hq : Measurable q)
    (hq0 : ∀ r, q r ≠ 0) (hqtop : ∀ r, q r ≠ ∞)
    (hm0 : ∀ r, (∫⁻ d, w r d ∂ν) ≠ 0)
    (hmtop : ∀ r, (∫⁻ d, w r d ∂ν) ≠ ∞)
    (hC : C ≠ ∞)
    (hQ : ∀ r, (∫⁻ d, w r d ∂ν) * (∫⁻ d, (w r d)⁻¹ ∂ν) ≤ C)
    (hsphere : (∫⁻ r, (q r * ∫⁻ d, w r d ∂ν)⁻¹ ∂μ) ≠ ∞) :
    uniformRayTest μ ν (fun r d => q r * w r d) := by
  let k : R → D → ℝ≥0∞ := fun r d => (q r * w r d)⁻¹
  have hk : Measurable (Function.uncurry k) := (hq.comp measurable_fst |>.mul hw).inv
  have hb : Measurable (fun r => (q r * ∫⁻ d, w r d ∂ν)⁻¹) :=
    (hq.mul hw.lintegral_prod_right).inv
  have hmean (r : R) : (∫⁻ d, k r d ∂ν) ≤ C * (q r * ∫⁻ d, w r d ∂ν)⁻¹ := by
    have h := mul_le_mul_left' (hQ r) (∫⁻ d, w r d ∂ν)⁻¹
    simp only [← mul_assoc, ENNReal.inv_mul_cancel (hm0 r) (hmtop r), one_mul] at h
    dsimp [k]
    simp_rw [ENNReal.mul_inv (Or.inl (hq0 r)) (Or.inl (hqtop r))]
    rw [lintegral_const_mul' _ _ (by simpa using hq0 r)]
    calc
      (q r)⁻¹ * (∫⁻ d, (w r d)⁻¹ ∂ν) ≤
          (q r)⁻¹ * ((∫⁻ d, w r d ∂ν)⁻¹*C) := mul_le_mul_left' h _
      _ = _ := by ac_rfl
  obtain ⟨M, hM, hpos⟩ := angular_mean_bound_gives_uniform_rays μ ν hk hb hC hsphere hmean
  refine ⟨{d | (∫⁻ r, k r d ∂μ) ≤ M}, ?_, hpos, M, hM, ?_⟩
  · exact measurableSet_le hk.lintegral_prod_left measurable_const
  · intro d hd
    exact hd

end BrownRadial
