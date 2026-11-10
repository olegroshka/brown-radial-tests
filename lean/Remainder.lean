import Analytic
import Mathlib.Analysis.Asymptotics.Defs

open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace BrownRadial

/-- A moving remainder, used to check the missing interchange hypothesis in
`prop:noR`. This is a counterexample to an analytic inference, not a claim
that these functions are remainders of a particular statistical model. -/
noncomputable def escapingBump (n : ℕ) : ℝ → ℝ :=
  (Ico (n : ℝ) (n+1)).indicator (fun _ => 1)

theorem escapingBump_integrable (n : ℕ) : Integrable (escapingBump n) := by
  exact (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => (1 : ℝ))
    (Ico (n : ℝ) (n+1))).integrable_indicator measurableSet_Ico

theorem escapingBump_integral (n : ℕ) : (∫ x, escapingBump n x) = 1 := by
  rw [escapingBump, integral_indicator measurableSet_Ico, integral_const,
    smul_eq_mul, measureReal_restrict_apply_univ]
  simp

theorem escapingBump_eventually_zero (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, escapingBump n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  exact indicator_of_notMem (fun h => (not_le_of_gt hx) h.1) _

noncomputable def movingRemainder (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ)+1)⁻¹^2 * escapingBump n x

theorem movingRemainder_pointwise_small (x : ℝ) :
    (fun n : ℕ => movingRemainder n x) =o[atTop] (fun n : ℕ => ((n : ℝ)+1)⁻¹^2) := by
  apply (isLittleO_zero (fun n : ℕ => ((n : ℝ)+1)⁻¹^2) atTop).congr'
    (hg := Filter.EventuallyEq.rfl)
  filter_upwards [escapingBump_eventually_zero x] with n hn
  simp [movingRemainder, hn]

theorem movingRemainder_integral (n : ℕ) :
    (∫ x, movingRemainder n x) = ((n : ℝ)+1)⁻¹^2 := by
  unfold movingRemainder
  rw [integral_const_mul, escapingBump_integral, mul_one]

/-- Pointwise o(N^-2) alone does not imply an integrated o(N^-2) bound. -/
theorem movingRemainder_integral_not_small :
    ¬ (fun n : ℕ => ∫ x, movingRemainder n x) =o[atTop]
      (fun n : ℕ => ((n : ℝ)+1)⁻¹^2) := by
  simp_rw [movingRemainder_integral]
  apply isLittleO_irrefl
  exact (Filter.Eventually.of_forall (fun n : ℕ =>
    ne_of_gt (by positivity : 0 < ((n : ℝ)+1)⁻¹^2))).frequently

end BrownRadial
