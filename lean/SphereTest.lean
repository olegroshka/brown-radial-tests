import Polar
import Capacity
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Brown's sphere test (`thm:brown`(d), the sphere-area parabolicity test) in its
potential-theoretic form: if the sphere integral diverges then the smooth
compact-support capacity of the unit ball vanishes. The radial test functions
are genuinely smooth: the optimal profile is approximated by a polynomial
times a smooth cutoff. No statistical statement is made here.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
namespace BrownRadial

/-- A nonnegative continuous function that is not integrable on the half-line
has arbitrarily large partial integrals. -/
theorem exists_large_interval_integral {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ r, 0 ≤ h r) (hdiv : ¬ IntegrableOn h (Ici 1)) (M : ℝ) :
    ∃ S : ℝ, 2 < S ∧ M < ∫ r in (2 : ℝ)..S, h r := by
  by_contra hcon
  push_neg at hcon
  apply hdiv
  have h2 : IntegrableOn h (Ioi 2) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (I := M) (a := 2)
      (b := fun n : ℕ => (n : ℝ) + 3) (l := atTop)
    · intro i
      exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    · filter_upwards with n
      simp only [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact hcon _ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h1 : IntegrableOn h (Icc 1 2) := hc.continuousOn.integrableOn_Icc
  rw [← Icc_union_Ioi_eq_Ici (by norm_num : (1 : ℝ) ≤ 2)]
  exact h1.union h2

theorem polynomial_eval_contDiff (p : Polynomial ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)

/-- Smooth cutoff equal to one on `[2, T-1]` and vanishing outside `(1, T)`. -/
noncomputable def radialCutoff (T r : ℝ) : ℝ :=
  Real.smoothTransition (r - 1) * Real.smoothTransition (T - r)

theorem radialCutoff_contDiff (T : ℝ) : ContDiff ℝ ∞ (radialCutoff T) := by
  unfold radialCutoff
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem radialCutoff_nonneg (T r : ℝ) : 0 ≤ radialCutoff T r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem radialCutoff_le_one (T r : ℝ) : radialCutoff T r ≤ 1 := by
  unfold radialCutoff
  have h1 := Real.smoothTransition.le_one (r - 1)
  have h2 := Real.smoothTransition.le_one (T - r)
  have h3 := Real.smoothTransition.nonneg (r - 1)
  have h4 := Real.smoothTransition.nonneg (T - r)
  nlinarith

theorem radialCutoff_eq_zero {T r : ℝ} (h : r ≤ 1 ∨ T ≤ r) : radialCutoff T r = 0 := by
  unfold radialCutoff
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := T - r) (by linarith), mul_zero]

theorem radialCutoff_eq_one {T r : ℝ} (h1 : 2 ≤ r) (h2 : r ≤ T - 1) : radialCutoff T r = 1 := by
  unfold radialCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- One-dimensional core of the sphere test: if the reciprocal of a positive
continuous area profile is not integrable at infinity, there are smooth radial
profiles, equal to one up to radius one and eventually zero, of arbitrarily
small weighted energy. -/
theorem exists_radial_profile {a : ℝ → ℝ} (ha : Continuous a) (hpos : ∀ r, 1 ≤ r → 0 < a r)
    (hdiv : ¬ IntegrableOn (fun r => 1 / a r) (Ici 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ (∀ r, r ≤ 1 → G r = 1) ∧ (∃ T : ℝ, ∀ r, T ≤ r → G r = 0) ∧
      (∫ r in Ioi (0 : ℝ), (deriv G r)^2 * a r) ≤ ε := by
  set h : ℝ → ℝ := fun r => 1 / a (max r 1) with hh
  have hcont : Continuous h := continuous_const.div (ha.comp (continuous_id.max continuous_const))
    (fun r => (hpos _ (le_max_right _ _)).ne')
  have hhpos : ∀ r, 0 < h r := fun r => one_div_pos.mpr (hpos _ (le_max_right _ _))
  have heq : ∀ r, 1 ≤ r → h r = 1 / a r := fun r hr => by simp only [hh, max_eq_left hr]
  have hdiv' : ¬ IntegrableOn h (Ici 1) := fun hi =>
    hdiv (hi.congr_fun (fun r hr => heq r hr) measurableSet_Ici)
  obtain ⟨S, hS2, hSM⟩ := exists_large_interval_integral hcont (fun r => (hhpos r).le) hdiv'
    (max (9/ε) 1)
  set T : ℝ := S + 1 with hT
  have h1T : (1 : ℝ) ≤ T := by linarith
  obtain ⟨r0, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr h1T) hcont.continuousOn
  have hm : 0 < h r0 := hhpos r0
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 1 T h hcont.continuousOn (h r0 / 2)
    (by positivity)
  have hpb : ∀ r ∈ Icc 1 T, h r / 2 ≤ p.eval r ∧ p.eval r ≤ 3/2 * h r := by
    intro r hr
    have h1 := abs_lt.mp (hp r hr)
    have h2 : h r0 ≤ h r := hmin hr
    constructor <;> linarith [h1.1, h1.2]
  set g : ℝ → ℝ := fun r => p.eval r * radialCutoff T r with hg
  have hgs : ContDiff ℝ ∞ g := (polynomial_eval_contDiff p).mul (radialCutoff_contDiff T)
  have hgc : Continuous g := hgs.continuous
  have hg0 : ∀ r, r ≤ 1 ∨ T ≤ r → g r = 0 := fun r hr => by
    simp only [hg]
    rw [radialCutoff_eq_zero hr, mul_zero]
  have hglo : ∀ r ∈ Icc 1 T, h r / 2 * radialCutoff T r ≤ g r := fun r hr =>
    mul_le_mul_of_nonneg_right (hpb r hr).1 (radialCutoff_nonneg T r)
  have hghi : ∀ r ∈ Icc 1 T, g r ≤ 3/2 * h r * radialCutoff T r := fun r hr =>
    mul_le_mul_of_nonneg_right (hpb r hr).2 (radialCutoff_nonneg T r)
  set P : ℝ → ℝ := fun r => ∫ t in (1 : ℝ)..r, g t with hP
  have hPd : ∀ r, HasDerivAt P (g r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable (μ := volume) _ _)
      (hgc.stronglyMeasurableAtFilter volume _) hgc.continuousAt
  have hPs : ContDiff ℝ ∞ P := contDiff_infty_iff_deriv.mpr
    ⟨fun r => (hPd r).differentiableAt, by
      rw [show deriv P = g from funext fun r => (hPd r).deriv]
      exact hgs⟩
  have hhχc : Continuous (fun t => h t * radialCutoff T t) :=
    hcont.mul (radialCutoff_contDiff T).continuous
  set X : ℝ := ∫ t in (1 : ℝ)..T, h t * radialCutoff T t with hX
  have hXlow : (∫ r in (2 : ℝ)..S, h r) ≤ X := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (hhχc.intervalIntegrable (μ := volume) 1 2) (hhχc.intervalIntegrable (μ := volume) 2 S)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hhχc.intervalIntegrable (μ := volume) 1 S) (hhχc.intervalIntegrable (μ := volume) S T)
    have n1 : 0 ≤ ∫ t in (1 : ℝ)..2, h t * radialCutoff T t :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun t _ => mul_nonneg (hhpos t).le (radialCutoff_nonneg T t))
    have n2 : 0 ≤ ∫ t in S..T, h t * radialCutoff T t :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => mul_nonneg (hhpos t).le (radialCutoff_nonneg T t))
    have e3 : (∫ t in (2 : ℝ)..S, h t * radialCutoff T t) = ∫ t in (2 : ℝ)..S, h t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hS2.le] at ht
      dsimp only
      rw [radialCutoff_eq_one ht.1 (by linarith [ht.2]), mul_one]
    linarith
  have hXpos : max (9/ε) 1 < X := lt_of_lt_of_le hSM hXlow
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_right _ _) hXpos
  have hX9 : 9/ε < X := lt_of_le_of_lt (le_max_left _ _) hXpos
  have hIlow : X / 2 ≤ P T := by
    have hm := intervalIntegral.integral_mono_on h1T
      (f := fun t => (1/2 : ℝ) * (h t * radialCutoff T t)) (g := g)
      ((continuous_const.mul hhχc).intervalIntegrable (μ := volume) 1 T) (hgc.intervalIntegrable (μ := volume) 1 T)
      (fun r hr => by have := hglo r hr; linarith)
    rw [intervalIntegral.integral_const_mul] at hm
    simp only [hP]
    linarith
  have hI : 0 < P T := by linarith
  refine ⟨fun r => 1 - P r / P T, contDiff_const.sub (hPs.div_const _), ?_, ⟨T, ?_⟩, ?_⟩
  · intro r hr
    have hz : P r = 0 := by
      simp only [hP]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
      intro t ht
      rw [uIcc_of_ge hr] at ht
      exact hg0 t (Or.inl ht.2)
    simp only [hz, zero_div, sub_zero]
  · intro r hr
    have hz : P r = P T := by
      have e := intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable (μ := volume) 1 T) (hgc.intervalIntegrable (μ := volume) T r)
      have z : (∫ t in T..r, g t) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
          intervalIntegral.integral_zero]
        intro t ht
        rw [uIcc_of_le hr] at ht
        exact hg0 t (Or.inr ht.1)
      simp only [hP]
      linarith
    simp only [hz]
    rw [div_self hI.ne', sub_self]
  · have hderiv : ∀ r, deriv (fun r => 1 - P r / P T) r = -(g r / P T) := fun r =>
      (((hPd r).div_const (P T)).const_sub 1).deriv
    simp_rw [hderiv]
    have hzero : ∀ r ∈ Ioi (0 : ℝ) \ Icc 1 T, (-(g r / P T))^2 * a r = 0 := by
      intro r hr
      have hr2 := hr.2
      rw [mem_Icc, not_and_or, not_le, not_le] at hr2
      have hgz : g r = 0 := hg0 r (hr2.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))
      rw [hgz]
      simp
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (fun r hr => lt_of_lt_of_le one_pos hr.1) hzero,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1T]
    have hmono := intervalIntegral.integral_mono_on h1T
      (f := fun r => (-(g r / P T))^2 * a r)
      (g := fun r => (9/4) / (P T)^2 * (h r * radialCutoff T r))
      ((((hgc.div_const _).neg.pow 2).mul ha).intervalIntegrable (μ := volume) 1 T)
      ((continuous_const.mul hhχc).intervalIntegrable (μ := volume) 1 T)
      (fun r hr => by
        have hA : 0 < a r := hpos r hr.1
        have hH : h r * a r = 1 := by rw [heq r hr.1]; exact one_div_mul_cancel hA.ne'
        have hc0 := radialCutoff_nonneg T r
        have hc1 := radialCutoff_le_one T r
        have g0 : 0 ≤ g r :=
          le_trans (mul_nonneg (by linarith [hhpos r]) hc0) (hglo r hr)
        have s1 : (g r)^2 ≤ (3/2 * h r * radialCutoff T r)^2 :=
          pow_le_pow_left₀ g0 (hghi r hr) 2
        have s2 : (radialCutoff T r)^2 ≤ radialCutoff T r := by nlinarith
        have s3 : (3/2 * h r * radialCutoff T r)^2 ≤ 9/4 * (h r)^2 * radialCutoff T r := by
          have := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 9/4 * (h r)^2)
          calc (3/2 * h r * radialCutoff T r)^2 = 9/4 * (h r)^2 * (radialCutoff T r)^2 := by ring
            _ ≤ _ := this
        have s4 : (h r)^2 * a r = h r := by rw [sq, mul_assoc, hH, mul_one]
        calc (-(g r / P T))^2 * a r = (g r)^2 * a r / (P T)^2 := by ring
          _ ≤ (9/4 * (h r)^2 * radialCutoff T r) * a r / (P T)^2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (s1.trans s3) hA.le
          _ = 9/4 * ((h r)^2 * a r) * radialCutoff T r / (P T)^2 := by ring
          _ = 9/4 / (P T)^2 * (h r * radialCutoff T r) := by rw [s4]; ring)
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans ?_
    change 9/4 / (P T)^2 * X ≤ ε
    have hI2 : X^2/4 ≤ (P T)^2 := by nlinarith
    have hεX : 9 < X * ε := (div_lt_iff₀ hε).mp hX9
    have hX0 : 0 < X := lt_trans zero_lt_one hX1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h5 : ε * (X^2/4) ≤ ε * (P T)^2 := mul_le_mul_of_nonneg_left hI2 hε.le
    nlinarith [mul_pos (sub_pos.mpr hεX) hX0]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth radial profile that is constant near the origin defines a smooth
function on an inner product space. -/
theorem radial_test_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (h1 : ∀ r, r ≤ 1 → G r = 1) :
    ContDiff ℝ ∞ (fun x : E => G ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : E) one_pos] with y hy
    exact h1 _ (mem_ball_zero_iff.mp hy).le
  · exact hG.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- The gradient of a radial function is bounded by the radial derivative. -/
theorem radial_test_fderiv_le {G : ℝ → ℝ} (hG : Differentiable ℝ G)
    (h1 : ∀ r, r ≤ 1 → G r = 1) (x : E) :
    ‖fderiv ℝ (fun y : E => G ‖y‖) x‖ ≤ |deriv G ‖x‖| := by
  by_cases hx : x = 0
  · subst hx
    have hz : fderiv ℝ (fun y : E => G ‖y‖) 0 = 0 := by
      apply HasFDerivAt.fderiv
      apply (hasFDerivAt_const (1 : ℝ) (0 : E)).congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0 : E) one_pos] with y hy
      exact h1 _ (mem_ball_zero_iff.mp hy).le
    rw [hz, norm_zero]
    exact abs_nonneg _
  · have hn : HasFDerivAt (norm : E → ℝ) (fderiv ℝ norm x) x :=
      ((contDiffAt_norm (n := 1) ℝ hx).differentiableAt le_rfl).hasFDerivAt
    have hc := (hG ‖x‖).hasDerivAt.comp_hasFDerivAt x hn
    have he : fderiv ℝ (fun y : E => G ‖y‖) x = deriv G ‖x‖ • fderiv ℝ norm x := hc.fderiv
    rw [he, norm_smul, Real.norm_eq_abs]
    have hl : ‖fderiv ℝ (norm : E → ℝ) x‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E)) (x₀ := x)
    exact mul_le_of_le_one_right (abs_nonneg _) hl

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Energy of a smooth radial test function, bounded through polar integration
by the one-dimensional weighted energy of its profile. -/
theorem radial_energy_le {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 ≤ w x) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (h1 : ∀ r, r ≤ 1 → G r = 1) {T : ℝ} (hT : ∀ r, T ≤ r → G r = 0) :
    weightedEnergy μ (fun x => ENNReal.ofReal (w x)) (fun x : E => G ‖x‖) ≤
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ), (deriv G r)^2 * sphericalArea μ w r) := by
  have hdG : Continuous (deriv G) := hG.continuous_deriv (by simp)
  have hdz : ∀ r, T < r → deriv G r = 0 := by
    intro r hr
    have he : G =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs using hT s (le_of_lt hs)
    rw [he.deriv_eq]
    simp
  set f : E → ℝ := fun x => (deriv G ‖x‖)^2 * w x with hf
  have hfc : Continuous f := ((hdG.comp continuous_norm).pow 2).mul hw
  have hfs : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) T) (fun x hx => by
      have hx' : T < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hx
      simp [hf, hdz _ hx'])
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hle : weightedEnergy μ (fun x => ENNReal.ofReal (w x)) (fun x : E => G ‖x‖) ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    unfold weightedEnergy
    apply lintegral_mono
    intro x
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (hp x)
    have hb := radial_test_fderiv_le (hG.differentiable (by simp)) h1 x
    calc ‖fderiv ℝ (fun y : E => G ‖y‖) x‖^2 ≤ |deriv G ‖x‖|^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = (deriv G ‖x‖)^2 := sq_abs _
  refine hle.trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hp x))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_polar μ hfi]
  apply le_of_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hnorm (θ : sphere (0 : E) 1) : ‖r • θ.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp θ.property,
      mul_one]
  simp only [hf, hnorm, sphericalArea]
  rw [integral_const_mul]
  ring

/-- Brown's sphere test in potential-theoretic form (`thm:brown`(d), the
implication (ii) => (i) of `thm:A`): divergence of the sphere integral forces
the smooth compact-support capacity of the unit ball to vanish. -/
theorem sphere_test_capacity_zero {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (hdiv : ¬ IntegrableOn (fun r => 1 / sphericalArea μ w r) (Ici 1)) :
    weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1) = 0 := by
  apply le_antisymm _ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨G, hG, h1, ⟨T, hT⟩, hint⟩ := exists_radial_profile (sphericalArea_continuous μ hw)
    (fun r hr => sphericalArea_pos μ hw hp (lt_of_lt_of_le one_pos hr)) hdiv
    (ε := (ε : ℝ)) (by exact_mod_cast hε)
  have hmem : (fun x : E => G ‖x‖) ∈ capacityTests (closedBall (0 : E) 1) :=
    ⟨radial_test_contDiff hG h1,
      HasCompactSupport.intro (isCompact_closedBall (0 : E) T) (fun x hx => hT _ (by
        have hx' : T < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hx
        exact hx'.le)),
      fun x hx => (h1 _ (by simpa [mem_closedBall, dist_zero_right] using hx)).ge⟩
  calc weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1)
      ≤ weightedEnergy μ (fun x => ENNReal.ofReal (w x)) (fun x : E => G ‖x‖) :=
        iInf_le (fun u : capacityTests (closedBall (0 : E) 1) =>
          weightedEnergy μ (fun x => ENNReal.ofReal (w x)) u.val) ⟨_, hmem⟩
    _ ≤ ENNReal.ofReal (∫ r in Ioi (0 : ℝ), (deriv G r)^2 * sphericalArea μ w r) :=
        radial_energy_le μ hw (fun x => (hp x).le) hG h1 hT
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hint
    _ = 0 + ε := by simp

/-- The ball-volume test without any doubling or Poincare hypothesis (the
unconditional direction of `thm:volume`): divergence of the volume integral
forces zero capacity, through `cor:cs` and the sphere test. -/
theorem volume_test_capacity_zero {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (hdiv : ¬ IntegrableOn (fun r => r / weightedBallVolume μ w r) (Ici 1)) :
    weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1) = 0 :=
  sphere_test_capacity_zero μ hw hp (sphere_volume_corollary μ hw hp hdiv)

end BrownRadial
