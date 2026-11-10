import SphericalA2
import Capacity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Potential-theoretic content of Brown's ray test (`thm:brown`(e)): a set of
directions of positive surface measure with uniformly bounded ray resistance
forces positive capacity of the unit ball, for the smooth compact-support
capacity of `Capacity.lean`. Together with `spherical_A2_ray_test` this gives
the convergent case of `lem:a2` in capacity form. No statistical statement
(inadmissibility) is asserted here.
-/

open MeasureTheory Set Metric
open scoped ENNReal ContDiff
namespace BrownRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Polar integration for extended nonnegative measurable functions, with the
canonical surface measure induced by Haar measure. -/
theorem lintegral_polar {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x ∂μ) = ∫⁻ θ : sphere (0 : E) 1, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • θ.val)) ∂μ.toSphere := by
  let h := homeomorphUnitSphereProd E
  let g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ := fun p => F (h.symm p).val
  have hg : Measurable g :=
    hF.comp (measurable_subtype_coe.comp h.symm.continuous.measurable)
  calc
    (∫⁻ x, F x ∂μ) = ∫⁻ x : ({0}ᶜ : Set E), F x.val ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl F, restrict_compl_singleton]
    _ = ∫⁻ p, g p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      have he := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _) g
      change (∫⁻ x, F (h.symm (h x)).val ∂μ.comap Subtype.val) = _ at he
      simpa only [Homeomorph.symm_apply_apply] using he
    _ = ∫⁻ θ : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), F (r.val • θ.val)
        ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
      rw [lintegral_prod _ hg.aemeasurable]
      rfl
    _ = _ := by
      apply lintegral_congr
      intro θ
      have hm : Measurable (fun r : Ioi (0 : ℝ) => F (r.val • θ.val)) :=
        hF.comp (by fun_prop)
      simp only [Measure.volumeIoiPow]
      rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
      exact lintegral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • θ.val))

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Fundamental theorem of calculus along a ray: a smooth compactly supported
function that is at least one at the unit vector `θ` has total radial
variation at least one on `[1, ∞)`. -/
theorem ray_derivative_lintegral_ge_one {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (hcs : HasCompactSupport u) {θ : E} (hθ : ‖θ‖ = 1) (h1 : 1 ≤ u θ) :
    1 ≤ ∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal ‖fderiv ℝ u (r • θ)‖ := by
  obtain ⟨R, _, hzero⟩ := hcs.exists_pos_le_norm
  let T : ℝ := max R 1 + 1
  have hT1 : (1 : ℝ) ≤ T := by
    have := le_max_right R 1
    dsimp only [T]
    linarith
  have hTR : R ≤ T := by
    have := le_max_left R 1
    dsimp only [T]
    linarith
  have huT : u (T • θ) = 0 := by
    apply hzero
    rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact hTR
  let φ' : ℝ → ℝ := fun r => fderiv ℝ u (r • θ) θ
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => u (r • θ)) (φ' r) r := by
    intro r
    have hs : HasDerivAt (fun r : ℝ => r • θ) θ r := by
      simpa using (hasDerivAt_id r).smul_const θ
    exact ((hu.differentiable (by simp)) (r • θ)).hasFDerivAt.comp_hasDerivAt r hs
  have hcont : Continuous (fun r : ℝ => fderiv ℝ u (r • θ)) :=
    (hu.continuous_fderiv (by simp)).comp (by fun_prop)
  have hφc : Continuous φ' := hcont.clm_apply continuous_const
  have hgc : Continuous (fun r : ℝ => ‖fderiv ℝ u (r • θ)‖) := hcont.norm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hderiv r) (hφc.intervalIntegrable 1 T)
  have hle : (1 : ℝ) ≤ ∫ r in (1 : ℝ)..T, ‖fderiv ℝ u (r • θ)‖ := by
    have habs := intervalIntegral.abs_integral_le_integral_abs (f := φ') (μ := volume) hT1
    have hmono : (∫ r in (1 : ℝ)..T, |φ' r|) ≤ ∫ r in (1 : ℝ)..T, ‖fderiv ℝ u (r • θ)‖ := by
      apply intervalIntegral.integral_mono_on hT1 (hφc.abs.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _)
      intro r _
      have h := (fderiv ℝ u (r • θ)).le_opNorm θ
      rwa [hθ, mul_one, Real.norm_eq_abs] at h
    rw [hftc] at habs
    simp only [huT, one_smul, zero_sub, abs_neg] at habs
    have := le_abs_self (u θ)
    linarith
  rw [intervalIntegral.integral_of_le hT1] at hle
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal (∫ r in Ioc 1 T, ‖fderiv ℝ u (r • θ)‖) := ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ r in Ioc 1 T, ENNReal.ofReal ‖fderiv ℝ u (r • θ)‖ :=
      ofReal_integral_eq_lintegral_ofReal hgc.integrableOn_Ioc
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := lintegral_mono_set (fun r hr => hr.1.le)

/-- Pointwise weighted arithmetic--geometric mean inequality behind the
Cauchy--Schwarz step. -/
theorem ray_pointwise_amgm {a q m : ℝ} (hq : 0 < q) (hm : 0 < m) :
    ENNReal.ofReal a ≤ ENNReal.ofReal (m / 2) * (ENNReal.ofReal (a ^ 2) * ENNReal.ofReal q) +
      ENNReal.ofReal (1 / (2 * m)) * (ENNReal.ofReal q)⁻¹ := by
  have hreal : a ≤ m / 2 * (a ^ 2 * q) + 1 / (2 * m) * q⁻¹ := by
    have hx : 0 < m * q := mul_pos hm hq
    have hsq := sq_nonneg (m * q * a - 1)
    have he : m / 2 * (a ^ 2 * q) + 1 / (2 * m) * q⁻¹ - a =
        (m * q * a - 1) ^ 2 / (2 * (m * q)) := by
      field_simp
      ring
    have hnn : 0 ≤ (m * q * a - 1) ^ 2 / (2 * (m * q)) := by positivity
    linarith
  rw [← ENNReal.ofReal_inv_of_pos hq, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Cauchy--Schwarz along a ray in extended form: unit total variation and
resistance at most `m` force energy at least `1/m`. -/
theorem ray_cauchy_schwarz {g q : ℝ → ℝ} (hg : Measurable g)
    (hq : Measurable q) (hqpos : ∀ r ∈ Ici (1 : ℝ), 0 < q r) {m : ℝ} (hm : 0 < m)
    (hone : 1 ≤ ∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal (g r))
    (hres : (∫⁻ r in Ici (1 : ℝ), (ENNReal.ofReal (q r))⁻¹) ≤ ENNReal.ofReal m) :
    ENNReal.ofReal (1 / m) ≤
      ∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal ((g r) ^ 2) * ENNReal.ofReal (q r) := by
  set En := ∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal ((g r) ^ 2) * ENNReal.ofReal (q r) with hEn
  have hA : Measurable (fun r : ℝ => ENNReal.ofReal (m / 2) *
      (ENNReal.ofReal ((g r) ^ 2) * ENNReal.ofReal (q r))) := by fun_prop
  have hstep : (∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal (g r)) ≤
      ENNReal.ofReal (m / 2) * En + ENNReal.ofReal (1 / (2 * m)) *
        ∫⁻ r in Ici (1 : ℝ), (ENNReal.ofReal (q r))⁻¹ := by
    calc
      _ ≤ ∫⁻ r in Ici (1 : ℝ), (ENNReal.ofReal (m / 2) *
            (ENNReal.ofReal ((g r) ^ 2) * ENNReal.ofReal (q r)) +
          ENNReal.ofReal (1 / (2 * m)) * (ENNReal.ofReal (q r))⁻¹) :=
        setLIntegral_mono' measurableSet_Ici
          (fun r hr => ray_pointwise_amgm (hqpos r hr) hm)
      _ = _ := by
        rw [lintegral_add_left hA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hhalf : ENNReal.ofReal (1 / (2 * m)) * ENNReal.ofReal m = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hmain : 1 ≤ ENNReal.ofReal (m / 2) * En + ENNReal.ofReal (1 / 2) := by
    calc
      (1 : ℝ≥0∞) ≤ _ := hone
      _ ≤ _ := hstep
      _ ≤ ENNReal.ofReal (m / 2) * En + ENNReal.ofReal (1 / (2 * m)) * ENNReal.ofReal m :=
        add_le_add_left (mul_le_mul_left' hres _) _
      _ = _ := by rw [hhalf]
  by_cases htop : En = ⊤
  · rw [htop]
    exact le_top
  · have he : En = ENNReal.ofReal En.toReal := (ENNReal.ofReal_toReal htop).symm
    rw [he] at hmain ⊢
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (by norm_num),
      ENNReal.one_le_ofReal] at hmain
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hm]
    nlinarith

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Energy lower bound along one ray with resistance at most `m`. -/
theorem ray_energy_lower {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) (n : ℕ)
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hcs : HasCompactSupport u)
    {θ : E} (hθ : ‖θ‖ = 1) (h1 : 1 ≤ u θ) {m : ℝ} (hm : 0 < m)
    (hres : (∫⁻ r in Ici (1 : ℝ), (ENNReal.ofReal (r ^ n * w (r • θ)))⁻¹) ≤ ENNReal.ofReal m) :
    ENNReal.ofReal (1 / m) ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
      (ENNReal.ofReal (‖fderiv ℝ u (r • θ)‖ ^ 2) * ENNReal.ofReal (w (r • θ))) := by
  have hcf : Continuous (fun x => fderiv ℝ u x) := hu.continuous_fderiv (by simp)
  have hray : Continuous (fun r : ℝ => r • θ) := by fun_prop
  have hone := ray_derivative_lintegral_ge_one hu hcs hθ h1
  have hgm : Measurable (fun r : ℝ => ‖fderiv ℝ u (r • θ)‖) := (hcf.norm.comp hray).measurable
  have hqm : Measurable (fun r : ℝ => r ^ n * w (r • θ)) :=
    ((continuous_id.pow n).mul (hw.comp hray)).measurable
  have hcsz := ray_cauchy_schwarz (g := fun r : ℝ => ‖fderiv ℝ u (r • θ)‖)
    (q := fun r : ℝ => r ^ n * w (r • θ)) hgm hqm
    (fun r hr => mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hr) n) (hp _)) hm hone hres
  refine hcsz.trans ?_
  have hstep : (∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal (‖fderiv ℝ u (r • θ)‖ ^ 2) *
        ENNReal.ofReal (r ^ n * w (r • θ))) ≤
      ∫⁻ r in Ici (1 : ℝ), ENNReal.ofReal (r ^ n) *
        (ENNReal.ofReal (‖fderiv ℝ u (r • θ)‖ ^ 2) * ENNReal.ofReal (w (r • θ))) := by
    apply setLIntegral_mono' measurableSet_Ici
    intro r hr
    rw [ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one hr) n), mul_left_comm]
  have hsub : Ici (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun r hr =>
    mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (mem_Ici.mp hr))
  exact hstep.trans (lintegral_mono_set hsub)

/-- Brown's ray test in capacity form: uniformly bounded ray resistance on a
set of directions of positive surface measure gives positive capacity of the
closed unit ball, hence non-parabolicity in the sense of the paper. -/
theorem ray_test_capacity_pos {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (hray : uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ)) (sphereProbability μ)
      (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ E - 1) * w (r.val • θ.val)))) :
    0 < weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1) := by
  obtain ⟨Ω, hΩ, hΩpos, M, hM, hb⟩ := hray
  let m : ℝ := M.toReal + 1
  have hm : 0 < m := by
    have := ENNReal.toReal_nonneg (a := M)
    dsimp only [m]
    linarith
  have hMm : M ≤ ENNReal.ofReal m := by
    calc
      M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hM).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp only [m]; linarith)
  have hσ : μ.toSphere Ω ≠ 0 := by
    intro h0
    rw [sphereProbability, Measure.smul_apply, smul_eq_mul, h0, mul_zero] at hΩpos
    exact lt_irrefl _ hΩpos
  have hdir : ∀ u ∈ capacityTests (closedBall (0 : E) 1), ∀ θ ∈ Ω,
      ENNReal.ofReal (1 / m) ≤ ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        (ENNReal.ofReal (‖fderiv ℝ u (r • θ.val)‖ ^ 2) * ENNReal.ofReal (w (r • θ.val))) := by
    rintro u ⟨hu, hcs, hu1⟩ θ hθ
    have hθn : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    have hmem : θ.val ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall, dist_zero_right, hθn]
    have hres : (∫⁻ r in Ici (1 : ℝ),
        (ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1) * w (r • θ.val)))⁻¹) ≤ ENNReal.ofReal m := by
      have he := lintegral_subtype_comap (μ := (volume : Measure ℝ)) (s := Ici (1 : ℝ))
        measurableSet_Ici
        (fun r : ℝ => (ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1) * w (r • θ.val)))⁻¹)
      exact he.symm.le.trans ((hb θ hθ).trans hMm)
    exact ray_energy_lower hw hp _ hu hcs hθn (hu1 _ hmem) hm hres
  have hlow : ∀ u ∈ capacityTests (closedBall (0 : E) 1),
      ENNReal.ofReal (1 / m) * μ.toSphere Ω ≤
        weightedEnergy μ (fun x => ENNReal.ofReal (w x)) u := by
    intro u hu'
    have hu := hu'.1
    have hcf : Continuous (fun x => fderiv ℝ u x) := hu.continuous_fderiv (by simp)
    have hF : Measurable (fun x => ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x)) :=
      (hcf.norm.pow 2).measurable.ennreal_ofReal.mul hw.measurable.ennreal_ofReal
    unfold weightedEnergy
    rw [lintegral_polar μ hF, ← setLIntegral_const]
    exact (setLIntegral_mono' hΩ (hdir u hu')).trans (setLIntegral_le_lintegral _ _)
  unfold weightedCapacity
  exact lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hσ)
    (le_iInf fun u => hlow u.val u.property)

/-- `lem:a2`, convergent case, in capacity form: a bounded spherical A2 ratio
together with a convergent sphere integral gives positive capacity of the
unit ball. -/
theorem spherical_A2_capacity_pos {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) {C : ℝ}
    (hQ : ∀ r : ℝ, 1 ≤ r →
      (∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ) *
      (∫ θ : sphere (0 : E) 1, 1 / w (r • θ.val) ∂sphereProbability μ) ≤ C)
    (hsphere : IntegrableOn (fun r : ℝ => 1 / (r ^ (Module.finrank ℝ E - 1) *
      ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ)) (Ici 1)) :
    0 < weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1) :=
  ray_test_capacity_pos μ hw hp (spherical_A2_ray_test μ hw hp hQ hsphere)

end BrownRadial
