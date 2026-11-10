import BrownRadial
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Comparability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Every Gaussian measure has the exponential norm moments required by `lem:lip`. -/
theorem gaussian_integrable_exp_norm (μ : Measure E) [IsGaussian μ] (L : ℝ) :
    Integrable (fun z => Real.exp (L * ‖z‖)) μ := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hbound (z : E) : L * ‖z‖ ≤ C * ‖z‖^2 + L^2 / C := by
    have heq : (L^2/C)*C = L^2 := div_mul_cancel₀ _ (ne_of_gt hC)
    have hs := sq_nonneg (C * ‖z‖ - L)
    have ht := sq_nonneg (C * ‖z‖)
    nlinarith
  apply (hint.const_mul (Real.exp (L^2/C))).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [add_comm] using hbound z)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] in
/-- Spatial form of the pointwise comparison, derived from the actual
Lipschitz hypothesis on log w. -/
theorem lipschitz_log_translate_bounds {w : E → ℝ} {L : ℝ≥0}
    (hw : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x)))
    (x z : E) :
    Real.exp (-(L : ℝ)*‖z‖) * w x ≤ w (x+z) ∧
      w (x+z) ≤ Real.exp ((L : ℝ)*‖z‖) * w x := by
  have h := hlog.dist_le_mul (x+z) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h
  simpa [neg_mul] using log_comparison (hw (x+z)) (hw x) h

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] in
theorem continuous_of_lipschitz_log {w : E → ℝ} {L : ℝ≥0}
    (hw : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    Continuous w := by
  have h := Real.continuous_exp.comp hlog.continuous
  simpa only [Function.comp_def, Real.exp_log (hw _)] using h

/-- Integrability of every translated positive log-Lipschitz weight against
a Gaussian measure, rather than an assumed integrability hypothesis. -/
theorem gaussian_integrable_translate (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) (x : E) :
    Integrable (fun z => w (x+z)) μ := by
  have hc := continuous_of_lipschitz_log hw hlog
  apply ((gaussian_integrable_exp_norm μ (L : ℝ)).mul_const (w x)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (hw _)]
  exact (lipschitz_log_translate_bounds hw hlog x z).2

/-- Gaussian comparison constants from the paper, with positivity and both
integral bounds. Applies in particular to standard Gaussian noise on R^m. -/
theorem gaussian_weight_comparison (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) (x : E) :
    (0 < ∫ z, Real.exp (-(L : ℝ)*‖z‖) ∂μ) ∧
    (∫ z, Real.exp (-(L : ℝ)*‖z‖) ∂μ) * w x ≤ (∫ z, w (x+z) ∂μ) ∧
    (∫ z, w (x+z) ∂μ) ≤ (∫ z, Real.exp ((L : ℝ)*‖z‖) ∂μ) * w x := by
  have hminus := gaussian_integrable_exp_norm μ (-(L : ℝ))
  have hplus := gaussian_integrable_exp_norm μ (L : ℝ)
  have hwint := gaussian_integrable_translate μ hw hlog x
  refine ⟨integral_exp_pos hminus, ?_, ?_⟩
  · simpa only [integral_mul_const] using
      integral_mono (hminus.mul_const (w x)) hwint
        (fun z => (lipschitz_log_translate_bounds hw hlog x z).1)
  · simpa only [integral_mul_const] using
      integral_mono hwint (hplus.mul_const (w x))
        (fun z => (lipschitz_log_translate_bounds hw hlog x z).2)

/-- Gaussian averaging in the translation form used in the comparison proof. -/
noncomputable def gaussianAverage (μ : Measure E) (w : E → ℝ) (x : E) : ℝ :=
  ∫ z, w (x+z) ∂μ

theorem gaussianAverage_pos (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) (x : E) :
    0 < gaussianAverage μ w x := by
  have h := gaussian_weight_comparison μ hw hlog x
  exact (mul_pos h.1 (hw x)).trans_le h.2.1

/-- Averaging preserves the exact logarithmic Lipschitz constant. This proves
the bound before invoking any differentiability of Gaussian convolution. -/
theorem gaussianAverage_log_lipschitz (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    LipschitzWith L (fun x => Real.log (gaussianAverage μ w x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp := gaussianAverage_pos μ hw hlog
  have hi := gaussian_integrable_translate μ hw hlog
  have hb (z : E) :
      Real.exp (-((L : ℝ) * dist x y)) * w (y+z) ≤ w (x+z) ∧
      w (x+z) ≤ Real.exp ((L : ℝ) * dist x y) * w (y+z) := by
    apply log_comparison (hw _) (hw _)
    simpa only [Real.dist_eq, dist_add_right] using hlog.dist_le_mul (x+z) (y+z)
  have hlo := integral_mono ((hi y).const_mul (Real.exp (-((L : ℝ)*dist x y))))
    (hi x) (fun z => (hb z).1)
  have hhi := integral_mono (hi x)
    ((hi y).const_mul (Real.exp ((L : ℝ)*dist x y))) (fun z => (hb z).2)
  simp only [integral_const_mul] at hlo hhi
  change Real.exp (-((L : ℝ)*dist x y)) * gaussianAverage μ w y ≤ gaussianAverage μ w x at hlo
  change gaussianAverage μ w x ≤ Real.exp ((L : ℝ)*dist x y) * gaussianAverage μ w y at hhi
  rw [Real.dist_eq, abs_le]
  constructor
  · apply Real.exp_le_exp.mp
    rw [Real.exp_sub, Real.exp_log (hp x), Real.exp_log (hp y)]
    exact (le_div_iff₀ (hp y)).mpr hlo
  · apply Real.exp_le_exp.mp
    rw [Real.exp_sub, Real.exp_log (hp x), Real.exp_log (hp y)]
    exact (div_le_iff₀ (hp y)).mpr hhi

/-- Any actual Frechet derivative of the log marginal has norm at most L.
Differentiability is explicit, so this does not rely on totalized derivatives. -/
theorem gaussianAverage_log_derivative_bound (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x)))
    {x : E} {D : E →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun y => Real.log (gaussianAverage μ w y)) D x) :
    ‖D‖ ≤ (L : ℝ) := by
  rw [← hD.fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ (gaussianAverage_log_lipschitz μ hw hlog)

/-- The actual Gaussian average satisfies the extended-real comparison
hypotheses of the energy, capacity, variance, doubling, and resistance lemmas. -/
theorem gaussian_comparable_ennreal (μ : Measure E) [IsGaussian μ]
    {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    ∃ c C : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ x, c * ENNReal.ofReal (w x) ≤ ENNReal.ofReal (gaussianAverage μ w x)) ∧
      (∀ x, ENNReal.ofReal (gaussianAverage μ w x) ≤ C * ENNReal.ofReal (w x)) := by
  let c := ∫ z, Real.exp (-(L : ℝ)*‖z‖) ∂μ
  let C := ∫ z, Real.exp ((L : ℝ)*‖z‖) ∂μ
  have hc : 0 < c := integral_exp_pos (gaussian_integrable_exp_norm μ (-(L : ℝ)))
  have hC : 0 < C := integral_exp_pos (gaussian_integrable_exp_norm μ (L : ℝ))
  refine ⟨ENNReal.ofReal c, ENNReal.ofReal C, (ENNReal.ofReal_pos.mpr hc).ne',
    ENNReal.ofReal_ne_top, (ENNReal.ofReal_pos.mpr hC).ne', ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro x
    rw [← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (gaussian_weight_comparison μ hw hlog x).2.1
  · intro x
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal (gaussian_weight_comparison μ hw hlog x).2.2

/-- Gaussian smoothing preserves vanishing of the concrete smooth-test
capacity defined in this project, for every set and every base measure. -/
theorem gaussian_capacity_zero_iff (μ : Measure E) [IsGaussian μ]
    (η : Measure E) {w : E → ℝ} {L : ℝ≥0} (hw : ∀ x, 0 < w x)
    (hlog : LipschitzWith L (fun x => Real.log (w x))) (K : Set E) :
    weightedCapacity η (fun x => ENNReal.ofReal (w x)) K = 0 ↔
      weightedCapacity η (fun x => ENNReal.ofReal (gaussianAverage μ w x)) K = 0 := by
  obtain ⟨c, C, hc0, hc, hC0, hC, hlo, hhi⟩ := gaussian_comparable_ennreal μ hw hlog
  exact weightedCapacity_zero_iff η hc0 hc hC0 hC hlo hhi K

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] in
/-- The real-valued prior density defines a sigma-finite prior whenever its
base measure is sigma-finite, in particular for Euclidean Lebesgue measure. -/
theorem real_density_prior_sigmaFinite (η : Measure E) [SigmaFinite η] (w : E → ℝ) :
    SigmaFinite (η.withDensity (fun x => ENNReal.ofReal (w x))) := inferInstance

end BrownRadial
