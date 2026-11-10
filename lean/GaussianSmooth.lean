import MultivariateGaussian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace BrownRadial

universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def gaussianLaplace (γ : Measure E) (g : E → F) (x : E) : F :=
  ∫ y, Real.exp (⟪y, x⟫_ℝ) • g y ∂γ

omit [CompleteSpace F] in
/-- Exponential growth is integrable against every Gaussian exponential tilt. -/
theorem gaussianLaplace_integrable (γ : Measure E) [IsGaussian γ]
    {g : E → F} (hg : Continuous g) {C A : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ y, ‖g y‖ ≤ C * Real.exp (A * ‖y‖)) (x : E) :
    Integrable (fun y => Real.exp (⟪y, x⟫_ℝ) • g y) γ := by
  apply ((gaussian_integrable_exp_norm γ (A + ‖x‖)).const_mul C).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro y
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (‖y‖ * ‖x‖) * (C * Real.exp (A * ‖y‖)) :=
      mul_le_mul (Real.exp_le_exp.mpr (real_inner_le_norm y x)) (hb y) (norm_nonneg _) (by positivity)
    _ = C * Real.exp ((A + ‖x‖) * ‖y‖) := by rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]; congr 2; ring

noncomputable def gaussianLaplaceMoment (g : E → F) (y : E) : E →L[ℝ] F :=
  (innerSL ℝ y).smulRight (g y)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] [CompleteSpace F] in
theorem gaussianLaplaceMoment_continuous {g : E → F} (hg : Continuous g) :
    Continuous (gaussianLaplaceMoment g) := by
  unfold gaussianLaplaceMoment
  change Continuous (fun y => ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ y) (g y))
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] [CompleteSpace F] in
theorem gaussianLaplaceMoment_bound {g : E → F} {C A : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ y, ‖g y‖ ≤ C * Real.exp (A * ‖y‖)) (y : E) :
    ‖gaussianLaplaceMoment g y‖ ≤ C * Real.exp ((A+1)*‖y‖) := by
  rw [gaussianLaplaceMoment, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hy : ‖y‖ ≤ Real.exp ‖y‖ := by linarith [Real.add_one_le_exp ‖y‖]
  calc
    _ ≤ Real.exp ‖y‖ * (C * Real.exp (A * ‖y‖)) :=
      mul_le_mul hy (hb y) (norm_nonneg _) (by positivity)
    _ = C * Real.exp ((A+1)*‖y‖) := by rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]; congr 2; ring

omit [CompleteSpace F] in
/-- Differentiation of the Gaussian Laplace integral with a proved uniform
integrable bound on the derivative in a neighborhood of each parameter. -/
theorem gaussianLaplace_hasFDerivAt (γ : Measure E) [IsGaussian γ]
    {g : E → F} (hg : Continuous g) {C A : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, ‖g y‖ ≤ C * Real.exp (A * ‖y‖)) (x₀ : E) :
    HasFDerivAt (gaussianLaplace γ g) (gaussianLaplace γ (gaussianLaplaceMoment g) x₀) x₀ := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun x y => Real.exp (⟪y, x⟫_ℝ) • gaussianLaplaceMoment g y)
    (bound := fun y => C * Real.exp ((A + ‖x₀‖ + 2) * ‖y‖)) (ε := 1) zero_lt_one
  · exact Filter.Eventually.of_forall fun x => by fun_prop
  · exact gaussianLaplace_integrable γ hg hC hb x₀
  · have hG := gaussianLaplaceMoment_continuous hg
    exact ((Real.continuous_exp.comp (continuous_id.inner continuous_const)).smul hG).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro y x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h := norm_sub_norm_le x x₀
      rw [mem_ball, dist_eq_norm] at hx
      linarith
    calc
      _ ≤ Real.exp (‖y‖ * (‖x₀‖+1)) * (C * Real.exp ((A+1)*‖y‖)) := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr ((real_inner_le_norm y x).trans
            (mul_le_mul_of_nonneg_left hx' (norm_nonneg _)))
        · exact gaussianLaplaceMoment_bound hC hb y
        · exact norm_nonneg _
        · positivity
      _ = C * Real.exp ((A+‖x₀‖+2)*‖y‖) := by
        rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]
        congr 2; ring
  · exact (gaussian_integrable_exp_norm γ _).const_mul C
  · apply Filter.Eventually.of_forall
    intro y x hx
    have h := (((innerSL ℝ y).hasFDerivAt (x := x)).exp).smul_const (g y)
    convert h using 1
    ext v
    simp [gaussianLaplaceMoment, smul_smul]

/-- Gaussian Laplace integration is smooth for continuous vector-valued
functions of at most exponential growth. No derivatives of the input occur. -/
theorem gaussianLaplace_contDiff_nat (γ : Measure E) [IsGaussian γ] (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {g : E → F}, Continuous g → ∀ {C A : ℝ}, 0 ≤ C →
      (∀ y, ‖g y‖ ≤ C * Real.exp (A * ‖y‖)) → ContDiff ℝ n (gaussianLaplace γ g) := by
  induction n with
  | zero =>
      intro F _ _ _ g hg C A hC hb
      apply contDiff_zero.mpr
      exact Differentiable.continuous (𝕜 := ℝ)
        (fun x => (gaussianLaplace_hasFDerivAt γ hg hC hb x).differentiableAt)
  | succ n ih =>
      intro F _ _ _ g hg C A hC hb
      rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp]
      apply contDiff_succ_iff_hasFDerivAt.mpr
      exact ⟨gaussianLaplace γ (gaussianLaplaceMoment g),
        ih (gaussianLaplaceMoment_continuous hg) hC (gaussianLaplaceMoment_bound hC hb),
        gaussianLaplace_hasFDerivAt γ hg hC hb⟩

theorem gaussianLaplace_contDiff (γ : Measure E) [IsGaussian γ]
    {g : E → F} (hg : Continuous g) {C A : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, ‖g y‖ ≤ C * Real.exp (A * ‖y‖)) :
    ContDiff ℝ ∞ (gaussianLaplace γ g) :=
  contDiff_infty.mpr fun n => gaussianLaplace_contDiff_nat γ n hg hC hb

end BrownRadial

namespace BrownRadial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem euclideanGaussianDensity_sub (x y : EuclideanSpace ℝ ι) :
    euclideanGaussianDensity (x-y) = Real.exp (-‖x‖^2/2) *
      (Real.exp (⟪y, x⟫_ℝ) * euclideanGaussianDensity y) := by
  have h : -‖x-y‖^2/2 = -‖x‖^2/2 + ⟪y, x⟫_ℝ + -‖y‖^2/2 := by
    rw [norm_sub_sq_real, real_inner_comm y x]
    ring
  simp only [euclideanGaussianDensity, h, Real.exp_add]
  ring

omit [DecidableEq ι] in
/-- Completing the square represents the actual normal marginal as a smooth
Gaussian Laplace transform times a smooth scalar factor. -/
theorem standardGaussianAverage_eq_laplace {w : EuclideanSpace ℝ ι → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (x : EuclideanSpace ℝ ι) :
    gaussianAverage standardEuclideanGaussian w x =
      Real.exp (-‖x‖^2/2) * gaussianLaplace standardEuclideanGaussian w x := by
  rw [standardEuclideanGaussianAverage_eq_marginal hw hw0,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    gaussianLaplace, standardEuclideanGaussian_eq_density,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun y : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensity y)) by
        unfold euclideanGaussianDensity; fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (hw0 y), ENNReal.toReal_ofReal (euclideanGaussianDensity_pos y).le,
    euclideanGaussianDensity_sub]
  simp only [smul_eq_mul]
  ring

/-- A positive log-Lipschitz weight has a genuinely smooth standard Gaussian
marginal in every finite dimension, including at nondifferentiable valleys. -/
theorem standardGaussianAverage_contDiff {w : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    ContDiff ℝ ∞ (gaussianAverage standardEuclideanGaussian w) := by
  have hw := continuous_of_lipschitz_log hp hlog
  have hb (y : EuclideanSpace ℝ ι) : ‖w y‖ ≤ w 0 * Real.exp ((L : ℝ) * ‖y‖) := by
    simpa only [zero_add, Real.norm_eq_abs, abs_of_pos (hp y), mul_comm]
      using (lipschitz_log_translate_bounds hp hlog 0 y).2
  have hg := gaussianLaplace_contDiff standardEuclideanGaussian hw (hp 0).le hb
  have he : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => Real.exp (-‖x‖^2/2)) :=
    ((contDiff_norm_sq ℝ).neg.div_const 2).exp
  convert he.mul hg using 1
  funext x
  exact standardGaussianAverage_eq_laplace hw.measurable (fun y => (hp y).le) x

theorem standardGaussianAverage_log_contDiff {w : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    ContDiff ℝ ∞ (fun x => Real.log (gaussianAverage standardEuclideanGaussian w x)) :=
  (standardGaussianAverage_contDiff hp hlog).log
    (fun x => (gaussianAverage_pos standardEuclideanGaussian hp hlog x).ne')

/-- Bounded drift with an actual gradient: smoothness has been proved, so
there is no supplied derivative hypothesis or reliance on a default derivative. -/
theorem standardGaussianAverage_bounded_drift {w : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x)))
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y => Real.log (gaussianAverage standardEuclideanGaussian w y))
      (gradient (fun y => Real.log (gaussianAverage standardEuclideanGaussian w y)) x) x ∧
      ‖gradient (fun y => Real.log (gaussianAverage standardEuclideanGaussian w y)) x‖ ≤ L := by
  have hd := (standardGaussianAverage_log_contDiff hp hlog).differentiable (by simp)
  refine ⟨(hd x).hasGradientAt, ?_⟩
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact gaussianAverage_log_derivative_bound standardEuclideanGaussian hp hlog (hd x).hasFDerivAt

/-- Integrability of the likelihood under the actual multivariate prior. -/
theorem standardGaussian_marginal_integrable {w : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x)))
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun θ => euclideanGaussianDensity (x-θ))
      (volume.withDensity (fun z => ENNReal.ofReal (w z))) := by
  apply density_marginal_integrable volume
    (show Measurable (euclideanGaussianDensity : EuclideanSpace ℝ ι → ℝ) by
      unfold euclideanGaussianDensity; fun_prop)
    (fun y => (euclideanGaussianDensity_pos y).le) euclideanGaussianDensity_even
    (continuous_of_lipschitz_log hp hlog).measurable (fun y => (hp y).le)
  rw [← standardEuclideanGaussian_eq_density]
  exact gaussian_integrable_translate standardEuclideanGaussian hp hlog x

end BrownRadial
