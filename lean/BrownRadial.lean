import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
First checked ingredients for `paper/radial-tests.tex`.
These are components, not a formalization of the full paper. In particular,
no recurrence, Gaussian regularity, or all-ball Poincare theorem is claimed.
-/
namespace BrownRadial

/-- The index shift in `cor:cs`: shifting the dyadic denominator changes
summability only by a factor four and one initial term. No doubling is needed. -/
theorem dyadic_shift_summable_iff (V : ℕ → ℝ) :
    Summable (fun j : ℕ => (4 : ℝ)^j / V (j + 1)) ↔
      Summable (fun j : ℕ => (4 : ℝ)^j / V j) := by
  have heq : (fun j : ℕ => (4 : ℝ)^(j + 1) / V (j + 1)) =
      (fun j : ℕ => 4 * ((4 : ℝ)^j / V (j + 1))) := by
    funext j
    rw [pow_succ]
    ring
  have hshift : Summable (fun j : ℕ => (4 : ℝ)^(j + 1) / V (j + 1)) ↔
      Summable (fun j : ℕ => (4 : ℝ)^j / V j) :=
    summable_nat_add_iff (f := fun j : ℕ => (4 : ℝ)^j / V j) 1
  rw [heq, summable_mul_left_iff (by norm_num : (4 : ℝ) ≠ 0)] at hshift
  exact hshift

/-- Series part of `cor:cs`, conditional on the analytic annulus bounds.
`v` and `s` represent the volume and sphere integrals on successive annuli. -/
theorem sphere_series_diverges (V v s : ℕ → ℝ)
    (hV : ∀ j, 0 < V j) (hv : ∀ j, 0 ≤ v j)
    (hupper : ∀ j, v j ≤ 2 * ((4 : ℝ)^j / V j))
    (hlower : ∀ j, (4 : ℝ)^j / V (j + 1) ≤ s j)
    (hdiv : ¬ Summable v) : ¬ Summable s := by
  intro hs
  have ht : Summable (fun j : ℕ => (4 : ℝ)^j / V (j + 1)) :=
    Summable.of_nonneg_of_le
      (fun j => div_nonneg (pow_nonneg (by norm_num) j) (le_of_lt (hV (j + 1))))
      hlower hs
  have hu := (dyadic_shift_summable_iff V).mp ht
  exact hdiv (Summable.of_nonneg_of_le hv hupper (hu.mul_left 2))

/-- Pointwise step of `lem:lip`. The log difference bound is the instance
of the Lipschitz hypothesis at the two points under consideration. -/
theorem log_comparison {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log a - Real.log b| ≤ t) :
    Real.exp (-t) * b ≤ a ∧ a ≤ Real.exp t * b := by
  have hlo := Real.exp_le_exp.mpr (abs_le.mp h).1
  have hhi := Real.exp_le_exp.mpr (abs_le.mp h).2
  rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb] at hlo hhi
  exact ⟨(le_div_iff₀ hb).mp hlo, (div_le_iff₀ hb).mp hhi⟩

open MeasureTheory

/-- Integration step used for mass and energy comparison in `lem:lip`.
Integrability is explicit: Lean's real integral is totalized. -/
theorem integral_comparison {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {c C : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlo : ∀ x, c * f x ≤ g x) (hhi : ∀ x, g x ≤ C * f x) :
    c * (∫ x, f x ∂μ) ≤ (∫ x, g x ∂μ) ∧
      (∫ x, g x ∂μ) ≤ C * (∫ x, f x ∂μ) := by
  constructor
  · simpa only [integral_const_mul] using integral_mono (hf.const_mul c) hg hlo
  · simpa only [integral_const_mul] using integral_mono hg (hf.const_mul C) hhi

/-- Energy densities inherit comparison because the squared gradient is nonnegative. -/
theorem energy_density_comparison {w v c C e : ℝ}
    (he : 0 ≤ e) (hlo : c * w ≤ v) (hhi : v ≤ C * w) :
    c * (e * w) ≤ e * v ∧ e * v ≤ C * (e * w) := by
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlo he,
    mul_le_mul_of_nonneg_left hhi he]

/-- Numerical separation bound in the local comparison of Theorem `thm:B`.
The geometric distance estimate is a premise, not silently asserted here. -/
theorem other_circle_clearance {s ρ d : ℝ}
    (hρ : ρ ≤ (3 / 20 : ℝ) * s) (hd : (7 / 10 : ℝ) * s - 3 * ρ ≤ d) :
    s / 4 ≤ d := by linarith

/-- Older-shell clearance in the same argument. -/
theorem older_shell_clearance {s ρ d : ℝ}
    (hρ : ρ ≤ (3 / 20 : ℝ) * s) (hd : s / 2 - ρ ≤ d) :
    (7 / 20 : ℝ) * s ≤ d := by linarith

/-- Far-case comparison of distances, with the paper's factor three. -/
theorem far_distance_comparison {τ ρ d dC : ℝ}
    (hfar : 2 * ρ ≤ τ) (hd : τ - ρ ≤ d) (hC : dC ≤ τ + ρ) :
    dC ≤ 3 * d := by linarith

/-- The elementary squared-error split in the gluing lemma `lem:glue`. -/
theorem gluing_square_split (u U m : ℝ) :
    (u - m)^2 ≤ 2 * (u - U)^2 + 2 * (U - m)^2 := by
  nlinarith [sq_nonneg (u - 2 * U + m)]

/-- Algebraic cancellation in `eq:k1`, with scalar curvature arbitrary. -/
theorem weighted_curvature_difference (R lapPhi gradSq : ℝ) :
    (R + 2 * lapPhi - gradSq) - R = 2 * lapPhi - gradSq := by ring

end BrownRadial
