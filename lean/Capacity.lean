import BrownRadial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory
open scoped ENNReal ContDiff
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The actual nonnegative Dirichlet energy, allowing infinite values. -/
noncomputable def weightedEnergy (μ : Measure E) (w : E → ℝ≥0∞) (u : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x‖^2) * w x ∂μ

/-- Smooth compactly supported test functions used in the paper's capacity. -/
def capacityTests (K : Set E) : Set (E → ℝ) :=
  {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ ∀ x ∈ K, 1 ≤ u x}

noncomputable def weightedCapacity (μ : Measure E) (w : E → ℝ≥0∞) (K : Set E) : ℝ≥0∞ :=
  ⨅ u : capacityTests K, weightedEnergy μ w u.val

theorem weightedEnergy_comparison (μ : Measure E) {w v : E → ℝ≥0∞}
    {c C : ℝ≥0∞} (hc : c ≠ ⊤) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x) (u : E → ℝ) :
    c * weightedEnergy μ w u ≤ weightedEnergy μ v u ∧
      weightedEnergy μ v u ≤ C * weightedEnergy μ w u := by
  unfold weightedEnergy
  rw [← lintegral_const_mul' c _ hc, ← lintegral_const_mul' C _ hC]
  constructor
  · apply lintegral_mono
    intro x
    simpa only [mul_left_comm] using mul_le_mul_left' (hlo x) (ENNReal.ofReal (‖fderiv ℝ u x‖^2))
  · apply lintegral_mono
    intro x
    simpa only [mul_left_comm] using mul_le_mul_left' (hhi x) (ENNReal.ofReal (‖fderiv ℝ u x‖^2))

/-- Full capacity comparison from `lem:lip` for the specified Dirichlet energy
and the same compact-support admissibility class, including infinite energies. -/
theorem weightedCapacity_comparison (μ : Measure E) {w v : E → ℝ≥0∞}
    {c C : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x) (K : Set E) :
    c * weightedCapacity μ w K ≤ weightedCapacity μ v K ∧
      weightedCapacity μ v K ≤ C * weightedCapacity μ w K := by
  unfold weightedCapacity
  rw [ENNReal.mul_iInf_of_ne hc0 hc, ENNReal.mul_iInf_of_ne hC0 hC]
  exact ⟨iInf_mono (fun u => (weightedEnergy_comparison μ hc hC hlo hhi u.val).1),
    iInf_mono (fun u => (weightedEnergy_comparison μ hc hC hlo hhi u.val).2)⟩

theorem weightedCapacity_zero_iff (μ : Measure E) {w v : E → ℝ≥0∞}
    {c C : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hlo : ∀ x, c*w x ≤ v x) (hhi : ∀ x, v x ≤ C*w x) (K : Set E) :
    weightedCapacity μ w K = 0 ↔ weightedCapacity μ v K = 0 := by
  have h := weightedCapacity_comparison μ hc0 hc hC0 hC hlo hhi K
  constructor
  · intro hw
    have hh := h.2
    rw [hw, mul_zero] at hh
    exact le_antisymm hh bot_le
  · intro hv
    have hh := h.1
    rw [hv] at hh
    exact (mul_eq_zero.mp (le_antisymm hh bot_le)).resolve_left hc0

end BrownRadial

namespace BrownRadial

/-- On real Hilbert spaces the energy's derivative norm is exactly the
gradient norm used in the paper. Capacity tests are smooth, so both are actual
derivatives on the entire admissibility class. -/
theorem weightedEnergy_eq_gradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    (μ : Measure H) (w : H → ℝ≥0∞) (u : H → ℝ) :
    weightedEnergy μ w u = ∫⁻ x, ENNReal.ofReal (‖gradient u x‖^2) * w x ∂μ := by
  unfold weightedEnergy gradient
  simp only [LinearIsometryEquiv.norm_map]

end BrownRadial

