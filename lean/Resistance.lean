import Comparability

open MeasureTheory
open scoped ENNReal
namespace BrownRadial

/-- Reciprocal-weight comparison retains infinite resistances. The measure
may be a ray measure or the radial measure used in the sphere test. -/
theorem resistance_comparison {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {w v : X → ℝ≥0∞} {c C : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ∞) (hC0 : C ≠ 0) (hC : C ≠ ∞)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x) :
    C⁻¹ * (∫⁻ x, (w x)⁻¹ ∂μ) ≤ (∫⁻ x, (v x)⁻¹ ∂μ) ∧
      (∫⁻ x, (v x)⁻¹ ∂μ) ≤ c⁻¹ * (∫⁻ x, (w x)⁻¹ ∂μ) := by
  rw [← lintegral_const_mul' C⁻¹ _ (by simpa using hC0),
    ← lintegral_const_mul' c⁻¹ _ (by simpa using hc0)]
  constructor
  · apply lintegral_mono
    intro x
    simpa only [ENNReal.mul_inv (Or.inl hC0) (Or.inl hC)] using
      ENNReal.inv_le_inv' (hhi x)
  · apply lintegral_mono
    intro x
    simpa only [ENNReal.mul_inv (Or.inl hc0) (Or.inl hc)] using
      ENNReal.inv_le_inv' (hlo x)

theorem resistance_finite_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {w v : X → ℝ≥0∞} {c C : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ∞) (hC0 : C ≠ 0) (hC : C ≠ ∞)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x) :
    (∫⁻ x, (w x)⁻¹ ∂μ) ≠ ∞ ↔ (∫⁻ x, (v x)⁻¹ ∂μ) ≠ ∞ := by
  have h := resistance_comparison μ hc0 hc hC0 hC hlo hhi
  constructor
  · intro hf
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simpa using hc0) hf) h.2
  · intro hf
    have hh : C⁻¹ * (∫⁻ x, (w x)⁻¹ ∂μ) ≠ ∞ := ne_top_of_le_ne_top hf h.1
    intro hinf
    rw [hinf, ENNReal.mul_top (by simpa using hC)] at hh
    exact hh rfl

/-- The analytic hypothesis of Brown's ray test, including a single uniform
bound on a measurable set of directions of positive measure. -/
def uniformRayTest {R D : Type*} [MeasurableSpace R] [MeasurableSpace D]
    (μ : Measure R) (ν : Measure D) (w : R → D → ℝ≥0∞) : Prop :=
  ∃ Ω : Set D, MeasurableSet Ω ∧ 0 < ν Ω ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧
    ∀ d ∈ Ω, (∫⁻ r, (w r d)⁻¹ ∂μ) ≤ M

theorem uniformRayTest_iff_of_comparison
    {R D : Type*} [MeasurableSpace R] [MeasurableSpace D]
    (μ : Measure R) (ν : Measure D) {w v : R → D → ℝ≥0∞} {c C : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ∞) (hC0 : C ≠ 0) (hC : C ≠ ∞)
    (hlo : ∀ r d, c*w r d ≤ v r d) (hhi : ∀ r d, v r d ≤ C*w r d) :
    uniformRayTest μ ν w ↔ uniformRayTest μ ν v := by
  have h (d : D) := resistance_comparison μ hc0 hc hC0 hC
    (fun r => hlo r d) (fun r => hhi r d)
  constructor
  · rintro ⟨Ω, hΩ, hpos, M, hM, hb⟩
    refine ⟨Ω, hΩ, hpos, c⁻¹*M, ENNReal.mul_ne_top (by simpa using hc0) hM, ?_⟩
    intro d hd
    exact (h d).2.trans (mul_le_mul_left' (hb d hd) _)
  · rintro ⟨Ω, hΩ, hpos, M, hM, hb⟩
    refine ⟨Ω, hΩ, hpos, C*M, ENNReal.mul_ne_top hC hM, ?_⟩
    intro d hd
    have hh := mul_le_mul_left' ((h d).1.trans (hb d hd)) C
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hC0 hC, one_mul] using hh

end BrownRadial
