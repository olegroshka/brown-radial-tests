import Polar
import Rays

open MeasureTheory Set Metric
open scoped ENNReal
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

noncomputable def sphereProbability : Measure (sphere (0 : E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

instance sphereProbability_isProbability : IsProbabilityMeasure (sphereProbability μ) := by
  haveI : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  unfold sphereProbability
  infer_instance

/-- The convergent half of the paper's spherical A2 lemma, with the actual
unit sphere, its normalized surface measure, radial Lebesgue measure on
[1,infinity), and the factor r^(dimension-1). The conclusion is precisely the
analytic ray-test hypothesis, prior to Brown's statistical theorem. -/
theorem spherical_A2_ray_test {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    {C : ℝ}
    (hQ : ∀ r : ℝ, 1 ≤ r →
      (∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ) *
      (∫ θ : sphere (0 : E) 1, 1/w (r • θ.val) ∂sphereProbability μ) ≤ C)
    (hsphere : IntegrableOn (fun r : ℝ => 1 / (r ^ (Module.finrank ℝ E-1) *
      ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ)) (Ici 1)) :
    uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ)) (sphereProbability μ)
      (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ E-1) * w (r.val • θ.val))) := by
  let ρ : Measure (Ici (1 : ℝ)) := volume.comap Subtype.val
  let ν := sphereProbability μ
  let n := Module.finrank ℝ E-1
  let m : ℝ → ℝ := fun r => ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂ν
  haveI : SigmaCompactSpace (Ici (1 : ℝ)) := isClosed_Ici.sigmaCompactSpace
  haveI : IsFiniteMeasureOnCompacts ρ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe measurableSet_Ici)
  haveI : SigmaFinite ρ := inferInstance
  have hpos (r : Ici (1 : ℝ)) : 0 < r.val := lt_of_lt_of_le zero_lt_one r.property
  have hi (r : ℝ) : Integrable (fun θ : sphere (0 : E) 1 => w (r • θ.val)) ν := by
    have hc : Continuous (fun θ : sphere (0 : E) 1 => w (r • θ.val)) := by fun_prop
    simpa using hc.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hinv (r : ℝ) : Integrable (fun θ : sphere (0 : E) 1 => 1/w (r • θ.val)) ν := by
    have hc : Continuous (fun θ : sphere (0 : E) 1 => 1/w (r • θ.val)) :=
      continuous_const.div (by fun_prop) (fun θ => (hp _).ne')
    simpa using hc.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hmpos (r : ℝ) : 0 < m r := by
    apply (integral_pos_iff_support_of_nonneg (fun θ => (hp _).le) (hi r)).mpr
    have he : Function.support (fun θ : sphere (0 : E) 1 => w (r • θ.val)) = univ := by
      ext θ
      simp [Function.mem_support, (hp _).ne']
    rw [he, measure_univ]
    exact zero_lt_one
  have hme (r : ℝ) : (∫⁻ θ : sphere (0 : E) 1, ENNReal.ofReal (w (r • θ.val)) ∂ν) =
      ENNReal.ofReal (m r) :=
    (ofReal_integral_eq_lintegral_ofReal (hi r) (Filter.Eventually.of_forall (fun θ => (hp _).le))).symm
  have hie (r : ℝ) : (∫⁻ θ : sphere (0 : E) 1, (ENNReal.ofReal (w (r • θ.val)))⁻¹ ∂ν) =
      ENNReal.ofReal (∫ θ : sphere (0 : E) 1, 1/w (r • θ.val) ∂ν) := by
    have he (θ : sphere (0 : E) 1) :
        (ENNReal.ofReal (w (r • θ.val)))⁻¹ = ENNReal.ofReal (1 / w (r • θ.val)) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (hp _)]
    simp_rw [he]
    exact (ofReal_integral_eq_lintegral_ofReal (hinv r)
      (Filter.Eventually.of_forall (fun θ => (one_div_pos.mpr (hp _)).le))).symm
  have hint : Integrable (fun r : Ici (1 : ℝ) => 1/(r.val^n*m r.val)) ρ :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hsphere
  have hkernel (r : Ici (1 : ℝ)) :
      (ENNReal.ofReal (r.val^n) * ∫⁻ θ : sphere (0 : E) 1,
        ENNReal.ofReal (w (r.val • θ.val)) ∂ν)⁻¹ = ENNReal.ofReal (1/(r.val^n*m r.val)) := by
    rw [hme, ← ENNReal.ofReal_mul (pow_pos (hpos r) n).le,
      ← ENNReal.ofReal_inv_of_pos (mul_pos (pow_pos (hpos r) n) (hmpos r.val)), one_div]
  have hfin : (∫⁻ r : Ici (1 : ℝ), (ENNReal.ofReal (r.val^n) * ∫⁻ θ : sphere (0 : E) 1,
      ENNReal.ofReal (w (r.val • θ.val)) ∂ν)⁻¹ ∂ρ) ≠ ∞ := by
    simp_rw [hkernel]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun r => (one_div_pos.mpr (mul_pos (pow_pos (hpos r) n) (hmpos r.val))).le))]
    exact ENNReal.ofReal_ne_top
  have h := bounded_angular_A2_gives_uniformRayTest ρ ν
    (w := fun r θ => ENNReal.ofReal (w (r.val • θ.val)))
    (q := fun r : Ici (1 : ℝ) => ENNReal.ofReal (r.val^n)) (C := ENNReal.ofReal C)
    (by fun_prop) (by fun_prop)
    (fun r => (ENNReal.ofReal_pos.mpr (pow_pos (hpos r) n)).ne')
    (fun _ => ENNReal.ofReal_ne_top)
    (fun r => by rw [hme]; exact (ENNReal.ofReal_pos.mpr (hmpos r.val)).ne')
    (fun r => by rw [hme]; exact ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    (fun r => by
      rw [hme, hie, ← ENNReal.ofReal_mul (hmpos r.val).le]
      exact ENNReal.ofReal_le_ofReal (hQ r.val r.property)) hfin
  simpa only [← ENNReal.ofReal_mul (pow_pos (hpos _) n).le] using h

end BrownRadial
