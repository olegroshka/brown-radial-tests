import Gaussian
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] in
/-- Translation averaging against an even density is precisely its marginal
against the density prior. Both sides use actual measures and integrals. -/
theorem average_eq_density_marginal (η : Measure E) [η.IsAddLeftInvariant]
    {φ w : E → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (heven : ∀ x, φ (-x) = φ x) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (x : E) :
    gaussianAverage (η.withDensity (fun z => ENNReal.ofReal (φ z))) w x =
      ∫ θ, φ (x-θ) ∂η.withDensity (fun z => ENNReal.ofReal (w z)) := by
  unfold gaussianAverage
  rw [integral_withDensity_eq_integral_toReal_smul hφ.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hφ0 _), ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  have h := integral_add_left_eq_self (μ := η) (fun θ => w θ * φ (x-θ)) x
  simpa only [sub_add_cancel_left, heven, mul_comm] using h

omit [NormedSpace ℝ E] in
/-- The same change of variables transfers integrability, so the marginal
identity can be used without relying on the default value of an integral. -/
theorem density_marginal_integrable (η : Measure E) [η.IsAddLeftInvariant]
    {φ w : E → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (heven : ∀ x, φ (-x) = φ x) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (x : E)
    (hi : Integrable (fun z => w (x+z)) (η.withDensity (fun z => ENNReal.ofReal (φ z)))) :
    Integrable (fun θ => φ (x-θ)) (η.withDensity (fun z => ENNReal.ofReal (w z))) := by
  have hi' := (integrable_withDensity_iff_integrable_smul' hφ.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  simp only [ENNReal.toReal_ofReal (hφ0 _), smul_eq_mul] at hi'
  apply (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  have he (θ : E) : φ (-x+θ) = φ (x-θ) := by
    rw [show -x+θ = -(x-θ) by abel, heven]
  simpa only [he, add_neg_cancel_left, mul_comm] using hi'.comp_add_left (-x)

/-- The explicit standard Euclidean Gaussian density. Normalization and its
`IsGaussian` instance in arbitrary dimension remain separate obligations. -/
noncomputable def euclideanGaussianDensity [FiniteDimensional ℝ E] (x : E) : ℝ :=
  ((Real.sqrt (2 * Real.pi)) ^ (Module.finrank ℝ E))⁻¹ * Real.exp (-‖x‖^2 / 2)

omit [MeasurableSpace E] [BorelSpace E] in
theorem euclideanGaussianDensity_pos [FiniteDimensional ℝ E] (x : E) :
    0 < euclideanGaussianDensity x := by
  unfold euclideanGaussianDensity
  positivity

omit [MeasurableSpace E] [BorelSpace E] in
theorem euclideanGaussianDensity_even [FiniteDimensional ℝ E] (x : E) :
    euclideanGaussianDensity (-x) = euclideanGaussianDensity x := by
  simp [euclideanGaussianDensity]

/-- The paper's multivariate density marginal equals the translation average
for the measure defined by that same explicit Gaussian density. This theorem
does not yet identify that measure with the abstract `IsGaussian` interface. -/
theorem euclideanGaussianAverage_eq_marginal [FiniteDimensional ℝ E]
    (η : Measure E) [η.IsAddLeftInvariant] {w : E → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (x : E) :
    gaussianAverage (η.withDensity (fun z => ENNReal.ofReal (euclideanGaussianDensity z))) w x =
      ∫ θ, euclideanGaussianDensity (x-θ) ∂η.withDensity (fun z => ENNReal.ofReal (w z)) := by
  apply average_eq_density_marginal η _ (fun z => (euclideanGaussianDensity_pos z).le)
    euclideanGaussianDensity_even hw hw0
  unfold euclideanGaussianDensity
  fun_prop

/-- In one dimension the concrete normal measure is already available in
Mathlib, so the density and the abstract Gaussian averaging are identified. -/
theorem gaussianRealAverage_eq_marginal {w : ℝ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (x : ℝ) :
    gaussianAverage (gaussianReal 0 1) w x =
      ∫ θ, gaussianPDFReal 0 1 (x-θ) ∂volume.withDensity (fun z => ENNReal.ofReal (w z)) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  change gaussianAverage (volume.withDensity (fun z => ENNReal.ofReal (gaussianPDFReal 0 1 z))) w x = _
  apply average_eq_density_marginal volume (measurable_gaussianPDFReal _ _)
    (fun z => gaussianPDFReal_nonneg _ _ _) _ hw hw0
  intro z
  simp [gaussianPDFReal]

/-- The one-dimensional prior marginal is integrable for positive
log-Lipschitz weights, with no separate integrability assumption. -/
theorem gaussianReal_marginal_integrable {w : ℝ → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x))) (x : ℝ) :
    Integrable (fun θ => gaussianPDFReal 0 1 (x-θ))
      (volume.withDensity (fun z => ENNReal.ofReal (w z))) := by
  apply density_marginal_integrable volume (measurable_gaussianPDFReal _ _)
    (fun z => gaussianPDFReal_nonneg _ _ _) (fun z => by simp [gaussianPDFReal])
    (continuous_of_lipschitz_log hp hlog).measurable (fun z => (hp z).le)
  have hi := gaussian_integrable_translate (gaussianReal 0 1) hp hlog x
  simpa only [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0), gaussianPDF] using hi

/-- The exact logarithmic Lipschitz bound holds for the actual density
marginal in one dimension. Smoothness is not asserted by this theorem. -/
theorem gaussianReal_marginal_log_lipschitz {w : ℝ → ℝ} {L : ℝ≥0}
    (hp : ∀ x, 0 < w x) (hlog : LipschitzWith L (fun x => Real.log (w x))) :
    LipschitzWith L (fun x => Real.log
      (∫ θ, gaussianPDFReal 0 1 (x-θ) ∂volume.withDensity (fun z => ENNReal.ofReal (w z)))) := by
  have h := gaussianAverage_log_lipschitz (gaussianReal 0 1) hp hlog
  simpa only [gaussianRealAverage_eq_marginal (continuous_of_lipschitz_log hp hlog).measurable
    (fun z => (hp z).le)] using h

end BrownRadial
