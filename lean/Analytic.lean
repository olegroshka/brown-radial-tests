import BrownRadial
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
namespace BrownRadial

/-- Reciprocal Cauchy--Schwarz on a finite measure space, proved by integrating
a nonnegative square. This supplies the analytic inequality used in `cor:cs`.
The integral of the positive weight is explicitly assumed positive. -/
theorem reciprocal_integral_cauchy_schwarz {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {a : X → ℝ}
    (ha : ∀ᵐ x ∂μ, 0 < a x) (hi : Integrable a μ)
    (hinv : Integrable (fun x => 1 / a x) μ)
    (hA : 0 < ∫ x, a x ∂μ) :
    (μ.real Set.univ)^2 ≤ (∫ x, a x ∂μ) * (∫ x, 1 / a x ∂μ) := by
  let A := ∫ x, a x ∂μ
  let M := μ.real Set.univ
  let t := M / A
  have hp : ∀ᵐ x ∂μ, 0 ≤ t^2 * a x - 2*t + 1 / a x := by
    filter_upwards [ha] with x hx
    have h := sq_nonneg (t * a x - 1)
    have hi' : (1 / a x) * a x = 1 := div_mul_cancel₀ 1 (ne_of_gt hx)
    apply (mul_nonneg_iff_of_pos_right hx).mp
    nlinarith
  have h : (0 : ℝ) ≤ ∫ x, (t^2 * a x - 2*t + 1 / a x) ∂μ := integral_nonneg_of_ae hp
  have hsub : Integrable (fun x => t^2 * a x - 2*t) μ :=
    (hi.const_mul (t^2)).sub (integrable_const (2*t))
  rw [integral_add hsub hinv] at h
  rw [integral_sub (f := fun x => t^2 * a x) (g := fun _ => 2*t)
    (hi.const_mul (t^2)) (integrable_const (2*t)), integral_const_mul,
    integral_const] at h
  change 0 ≤ t^2 * A - M * (2*t) + (∫ x, 1 / a x ∂μ) at h
  have ht : t * A = M := div_mul_cancel₀ M (ne_of_gt hA)
  have hmul := mul_nonneg h (le_of_lt hA)
  nlinarith [sq_nonneg (t*A-M)]

/-- The sphere-side annulus estimate in `cor:cs`, with the shell mass bounded
by the outer ball volume `U`. -/
theorem sphere_annulus_lower {a : ℝ → ℝ} {R U : ℝ}
    (hR : 0 < R) (hU : 0 < U) (ha : ∀ x ∈ Set.Icc R (2*R), 0 < a x)
    (hi : IntegrableOn a (Set.Icc R (2*R)))
    (hinv : IntegrableOn (fun x => 1 / a x) (Set.Icc R (2*R)))
    (hA : 0 < ∫ x in Set.Icc R (2*R), a x)
    (hmass : (∫ x in Set.Icc R (2*R), a x) ≤ U) :
    R^2 / U ≤ ∫ x in Set.Icc R (2*R), 1 / a x := by
  have h := reciprocal_integral_cauchy_schwarz
    (volume.restrict (Set.Icc R (2*R)))
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall ha)) hi hinv hA
  rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le (by linarith)] at h
  have hn : (0 : ℝ) ≤ ∫ x in Set.Icc R (2*R), 1 / a x :=
    setIntegral_nonneg measurableSet_Icc (fun x hx => le_of_lt (one_div_pos.mpr (ha x hx)))
  apply (div_le_iff₀ hU).mpr
  nlinarith [mul_le_mul_of_nonneg_right hmass hn]

/-- The volume-side annulus estimate in `cor:cs`. -/
theorem volume_annulus_upper {V : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hV : 0 < V R)
    (hmono : ∀ r ∈ Set.Icc R (2*R), V R ≤ V r)
    (hi : IntegrableOn (fun r => r / V r) (Set.Icc R (2*R))) :
    (∫ r in Set.Icc R (2*R), r / V r) ≤ 2*R^2 / V R := by
  have hbound (r : ℝ) (hr : r ∈ Set.Icc R (2*R)) : r / V r ≤ 2*R / V R := by
    apply (div_le_div_iff₀ (hV.trans_le (hmono r hr)) hV).mpr
    nlinarith [hmono r hr, hr.2,
      mul_le_mul_of_nonneg_right hr.2 (le_of_lt hV),
      mul_le_mul_of_nonneg_left (hmono r hr) (by linarith : 0 ≤ 2*R)]
  have h := setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Icc hbound
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Icc_of_le (by linarith : R ≤ 2*R)] at h
  convert h using 1; ring

/-- Integrated two-region variance lower bound from `lem:1d` (algebraic core). -/
theorem two_region_variance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (m : ℝ) :
    a*b/(a+b) ≤ a*m^2+b*(1-m)^2 := by
  apply (div_le_iff₀ (by positivity : 0 < a+b)).mpr
  nlinarith [sq_nonneg ((a+b)*m-b)]

theorem two_region_variance_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b / 2 ≤ a*b/(a+b) := by
  apply (le_div_iff₀ (by positivity : 0 < a+b)).mpr
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith

/-- Explicit constant in `lem:1d`, once its variance and energy bounds hold. -/
theorem one_dimensional_A2_constant {mass resistance C D r : ℝ}
    (hD : 0 < D) (hres : 0 < resistance)
    (h : mass / (2 * D^3) ≤ C * (4*r)^2 / resistance) :
    mass * resistance ≤ 32*C*D^3*r^2 := by
  have hd : 0 < 2*D^3 := by positivity
  have hh := (div_le_div_iff₀ hd hres).mp h
  nlinarith

/-- Counterexample to the inference in the doubling proof of `prop:wall`:
radius greater than half the center's distance does NOT imply intersection.
For a plane at normal coordinate zero, a ball centered at coordinate three
with radius two has all normal coordinates greater than one. It also misses
the entire slab with normal distance in [1/4, 1/2]. -/
theorem wall_straddling_counterexample :
    (2 : ℝ) > 3 / 2 ∧
    ∀ y : ℝ, |y - 3| < 2 → 1 < y ∧ ¬ (|y| ≤ 1 / 2) := by
  constructor
  · norm_num
  · intro y hy
    have hlo := (abs_lt.mp hy).1
    have hy1 : 1 < y := by linarith
    refine ⟨hy1, ?_⟩
    rw [abs_of_pos (by linarith : 0 < y)]
    linarith

end BrownRadial
