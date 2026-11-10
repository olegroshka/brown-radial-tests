import GaussianMarginal
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace BrownRadial

/-- Specifying the normal law of every linear image also identifies the mean
and variance required by Mathlib's Gaussian interface. -/
theorem isGaussian_of_normal_linear_images {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E)
    (h : ∀ L : E →L[ℝ] ℝ, ∃ m : ℝ, ∃ v : ℝ≥0, μ.map L = gaussianReal m v) :
    IsGaussian μ := by
  constructor
  intro L
  obtain ⟨m, v, he⟩ := h L
  have hm : (∫ x, L x ∂μ) = m := by
    rw [← integral_map (by fun_prop : AEMeasurable L μ)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (μ.map L)), he]
    exact integral_id_gaussianReal
  have hv : Var[L; μ] = (v : ℝ) := by
    rw [← variance_id_map (by fun_prop : AEMeasurable L μ), he]
    exact variance_id_gaussianReal
  simpa only [hm, hv, Real.toNNReal_coe] using he

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every linear image of independent standard normal coordinates is normal,
with variance the sum of squares of its coefficients. -/
theorem standardNormal_pi_linear_image (L : (ι → ℝ) →L[ℝ] ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L =
      gaussianReal 0 (∑ i, (L (Pi.single i 1)^2).toNNReal) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_eq_charFunDual_smul, charFunDual_pi, charFun_gaussianReal]
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, integral_continuousLinearMap_gaussianReal,
    variance_continuousLinearMap_gaussianReal]
  simp only [map_zero, Complex.ofReal_zero, zero_mul, zero_sub,
    NNReal.coe_one, mul_one, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.single_apply, smul_eq_mul, NNReal.coe_sum]
  rw [← Complex.exp_sum]
  congr 1
  simp (disch := positivity) only [Real.coe_toNNReal, mul_pow, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

instance standardNormal_pi_isGaussian :
    IsGaussian (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  isGaussian_of_normal_linear_images _ fun L =>
    ⟨0, ∑ i, (L (Pi.single i 1)^2).toNNReal, standardNormal_pi_linear_image L⟩

omit [DecidableEq ι] in
/-- Independent standard normal coordinates have the product of their
one-dimensional densities with respect to coordinate Lebesgue measure. -/
theorem standardNormal_pi_eq_density :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).restrict (s := s i)))
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  simp only [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]

omit [DecidableEq ι] in
/-- Cartesian factorization of the normalized Euclidean Gaussian density. -/
theorem euclideanGaussianDensity_eq_prod (x : EuclideanSpace ℝ ι) :
    euclideanGaussianDensity x = ∏ i, gaussianPDFReal 0 1 (x i) := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one,
    Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum,
    euclideanGaussianDensity, finrank_euclideanSpace, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_div, ← Finset.sum_neg_distrib, inv_pow,
    Fintype.card]

noncomputable def standardEuclideanGaussian : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (EuclideanSpace.equiv ι ℝ).symm

instance standardEuclideanGaussian_isGaussian :
    IsGaussian (standardEuclideanGaussian (ι := ι)) := by
  unfold standardEuclideanGaussian
  infer_instance

omit [DecidableEq ι] in
/-- The Gaussian law constructed from independent normal coordinates is
exactly the normalized Euclidean density against Lebesgue measure. -/
theorem standardEuclideanGaussian_eq_density :
    standardEuclideanGaussian (ι := ι) =
      volume.withDensity (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensity x)) := by
  unfold standardEuclideanGaussian
  rw [standardNormal_pi_eq_density]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun a : ι → ℝ => f ((EuclideanSpace.equiv ι ℝ).symm a)) by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by unfold euclideanGaussianDensity; fun_prop) hf]
  have h := (PiLp.volume_preserving_toLp ι).lintegral_comp_emb
    (EuclideanSpace.measurableEquiv ι).symm.measurableEmbedding
    (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensity x) * f x)
  simpa only [euclideanGaussianDensity_eq_prod, Pi.mul_apply] using h

/-- Normalization follows from the explicit Gaussian law, rather than an
assumed integral of the multivariate density. -/
theorem euclideanGaussianDensity_integral_one :
    (∫ x : EuclideanSpace ℝ ι, euclideanGaussianDensity x) = 1 := by
  have h : (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (euclideanGaussianDensity x)) = 1 := by
    have h' : (volume.withDensity (fun x : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (euclideanGaussianDensity x))) Set.univ = 1 := by
      rw [← standardEuclideanGaussian_eq_density]
      exact measure_univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h'
  have hi : Integrable (euclideanGaussianDensity : EuclideanSpace ℝ ι → ℝ) := by
    refine ⟨by unfold euclideanGaussianDensity; fun_prop, ?_⟩
    change (∫⁻ x : EuclideanSpace ℝ ι, ‖euclideanGaussianDensity x‖ₑ) < ⊤
    simpa only [Real.enorm_eq_ofReal (euclideanGaussianDensity_pos _).le, h] using ENNReal.one_lt_top
  rw [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun x => (euclideanGaussianDensity_pos x).le))
    zero_le_one, ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => (euclideanGaussianDensity_pos x).le), h, ENNReal.ofReal_one]

omit [DecidableEq ι] in
/-- The actual multivariate prior marginal is the Gaussian average already
used in the comparison, capacity and Poincare theorems. -/
theorem standardEuclideanGaussianAverage_eq_marginal {w : EuclideanSpace ℝ ι → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (x : EuclideanSpace ℝ ι) :
    gaussianAverage standardEuclideanGaussian w x =
      ∫ θ, euclideanGaussianDensity (x-θ) ∂volume.withDensity (fun z => ENNReal.ofReal (w z)) := by
  rw [standardEuclideanGaussian_eq_density]
  exact euclideanGaussianAverage_eq_marginal volume hw hw0 x

end BrownRadial
