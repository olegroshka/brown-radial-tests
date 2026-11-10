import Radial
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory Set Metric
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Polar integration for a general integrable weight, with canonical surface
measure induced by Haar measure, in every positive finite dimension. -/
theorem integral_polar {f : E → ℝ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ E-1) * (∫ θ : sphere (0 : E) 1, f (r • θ.val) ∂μ.toSphere) := by
  let h := homeomorphUnitSphereProd E
  let g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ := fun p => f (h.symm p).val
  have hi : Integrable (fun x : ({0}ᶜ : Set E) => f x.val) (μ.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have hg : Integrable g (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1))) := by
    apply (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding _) (g := g)).mp
    change Integrable (fun x => f (h.symm (h x)).val) (μ.comap Subtype.val)
    simpa only [Homeomorph.symm_apply_apply] using hi
  calc
    (∫ x, f x ∂μ) = ∫ x : ({0}ᶜ : Set E), f x.val ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = ∫ p, g p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
      have he := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) g
      change (∫ x, f (h.symm (h x)).val ∂μ.comap Subtype.val) = _ at he
      simpa only [Homeomorph.symm_apply_apply] using he
    _ = ∫ r : Ioi (0 : ℝ), ∫ θ : sphere (0 : E) 1, f (r.val • θ.val) ∂μ.toSphere
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
      simpa [g, h] using integral_prod_symm g hg
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const _).real_toNNReal)]
      rw [integral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => Real.toNNReal (r ^ (Module.finrank ℝ E-1)) •
          ∫ θ : sphere (0 : E) 1, f (r • θ.val) ∂μ.toSphere)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul]

noncomputable def sphericalArea (w : E → ℝ) (r : ℝ) : ℝ :=
  r ^ (Module.finrank ℝ E-1) * ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂μ.toSphere

omit [Nontrivial E] in
theorem sphericalArea_continuous {w : E → ℝ} (hw : Continuous w) :
    Continuous (sphericalArea μ w) := by
  have hi : Continuous (fun r : ℝ => ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂μ.toSphere) := by
    have hh := continuous_parametric_integral_of_continuous
      (μ := μ.toSphere) (f := fun (r : ℝ) (θ : sphere (0 : E) 1) => w (r • θ.val))
      (by fun_prop) (s := univ) isCompact_univ
    simpa using hh
  exact (continuous_id.pow _).mul hi

theorem sphericalArea_pos {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    {r : ℝ} (hr : 0 < r) : 0 < sphericalArea μ w r := by
  haveI : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  have hc : Continuous (fun θ : sphere (0 : E) 1 => w (r • θ.val)) := by fun_prop
  apply mul_pos (pow_pos hr _)
  have hi : Integrable (fun θ : sphere (0 : E) 1 => w (r • θ.val)) μ.toSphere := by
    simpa using hc.continuousOn.integrableOn_compact (μ := μ.toSphere) isCompact_univ
  apply (integral_pos_iff_support_of_nonneg (fun θ => (hp _).le) hi).mpr
  have he : Function.support (fun θ : sphere (0 : E) 1 => w (r • θ.val)) = univ := by
    ext θ
    simp [Function.mem_support, ne_of_gt (hp _)]
  rw [he]
  exact Measure.measure_univ_pos.mpr (NeZero.ne μ.toSphere)

/-- Weighted ball volume, defined directly on the ambient space. -/
noncomputable def weightedBallVolume (w : E → ℝ) (r : ℝ) : ℝ :=
  ∫ x in ball (0 : E) r, w x ∂μ

theorem weightedBallVolume_eq_cumulativeArea {w : E → ℝ} (hw : Continuous w)
    {R : ℝ} (hR : 0 ≤ R) :
    weightedBallVolume μ w R = cumulativeArea (sphericalArea μ w) R := by
  have hi : IntegrableOn w (ball (0 : E) R) μ :=
    (hw.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set
      ball_subset_closedBall
  have hpolar := integral_polar μ (hi.integrable_indicator measurableSet_ball)
  rw [integral_indicator measurableSet_ball] at hpolar
  change weightedBallVolume μ w R = _ at hpolar
  rw [hpolar]
  calc
    (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E-1) *
        (∫ θ : sphere (0 : E) 1, (ball (0 : E) R).indicator w (r • θ.val) ∂μ.toSphere)) =
        ∫ r in Ioi (0 : ℝ), (Iio R).indicator (sphericalArea μ w) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      have hnorm (θ : sphere (0 : E) 1) : ‖r • θ.val‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
          mem_sphere_zero_iff_norm.mp θ.property, mul_one]
      by_cases hlt : r < R
      · simp [Set.indicator, mem_ball, dist_zero_right, hnorm, hlt, sphericalArea]
      · simp [Set.indicator, mem_ball, dist_zero_right, hnorm, hlt]
    _ = ∫ r in Ioo (0 : ℝ) R, sphericalArea μ w r := by
      rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
    _ = cumulativeArea (sphericalArea μ w) R := by
      rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
        cumulativeArea, intervalIntegral.integral_of_le hR]

/-- The sphere/volume corollary for actual continuous positive weights in any
positive finite dimension, with ball and sphere integrals connected by polar
integration. Divergence means failure of integrability of the positive kernel. -/
theorem sphere_volume_corollary {w : E → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x)
    (hvolume : ¬ IntegrableOn (fun r => r / weightedBallVolume μ w r) (Ici 1)) :
    ¬ IntegrableOn (fun r => 1 / sphericalArea μ w r) (Ici 1) := by
  apply continuous_area_volume_diverges (sphericalArea_continuous μ hw)
    (fun r hr => sphericalArea_pos μ hw hp hr)
  intro hi
  apply hvolume
  apply hi.congr_fun (fun r hr => ?_) measurableSet_Ici
  rw [weightedBallVolume_eq_cumulativeArea μ hw (le_trans zero_le_one hr)]

/-- The same conclusion with the normalized spherical mean used in the paper.
The positive dimensional surface-area constant does not affect convergence. -/
theorem sphere_volume_corollary_normalized {w : E → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x)
    (hvolume : ¬ IntegrableOn (fun r => r / weightedBallVolume μ w r) (Ici 1)) :
    ¬ IntegrableOn (fun r => 1 / (r ^ (Module.finrank ℝ E-1) *
      ⨍ θ : sphere (0 : E) 1, w (r • θ.val) ∂μ.toSphere)) (Ici 1) := by
  intro hi
  apply sphere_volume_corollary μ hw hp hvolume
  have he (r : ℝ) : sphericalArea μ w r = μ.toSphere.real univ *
      (r ^ (Module.finrank ℝ E-1) * ⨍ θ : sphere (0 : E) 1, w (r • θ.val) ∂μ.toSphere) := by
    unfold sphericalArea
    rw [← measure_smul_average μ.toSphere (fun θ : sphere (0 : E) 1 => w (r • θ.val))]
    simp only [smul_eq_mul]
    ring
  simpa only [he, one_div, mul_inv_rev, mul_comm] using hi.const_mul (μ.toSphere.real univ)⁻¹

end BrownRadial
