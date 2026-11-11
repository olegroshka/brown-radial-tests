import LatticeDP
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
The Poincare inequality of Haar (Lebesgue) measure on balls, premise P0 of
the series, and the statements of `LatticeSmallBalls` and `LatticeDP` with
that premise discharged.

Route (the classical one for convex sets, here for a ball `B` of radius `r`
in a finite-dimensional real normed space of dimension `n`, Haar measure):

1. For `x, y` in the open ball, by the fundamental theorem of calculus on the
   segment and the Cauchy--Schwarz inequality on `[0, 1]`,
   `(u x - u y)^2 <= |x - y|^2 * int_0^1 |Du ((1 - t) y + t x)|^2 dt`.
2. The variational variance is at most `int_B (u x - u y)^2 dx` for every
   `y` in `B`; integrate over `y`.
3. Split `[0, 1]` at `1/2`. For `t >= 1/2` substitute in `x`, for `t <= 1/2`
   substitute in `y`: a homothety of ratio `c >= 1/2` centred in `B` maps `B`
   into `B` and scales the measure by `c^n >= 2^(-n)`.

The constant is `2^n * (2 r)^2 / r^2 = 2^(n + 2)`; `32` in three-space.
-/

open MeasureTheory Set Metric Module
open scoped NNReal ENNReal ContDiff

namespace BrownRadial

/-! ### One variable: Cauchy--Schwarz on the unit interval -/

/-- `(int_0^1 f)^2 <= int_0^1 f^2` for `f` continuous on `[0, 1]`. -/
theorem sq_unit_interval_integral_le {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    (∫ t in (0:ℝ)..1, f t) ^ 2 ≤ ∫ t in (0:ℝ)..1, (f t) ^ 2 := by
  have hf1 : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable_of_Icc zero_le_one
  have hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume 0 1 :=
    (hf.pow 2).intervalIntegrable_of_Icc zero_le_one
  set c : ℝ := ∫ t in (0:ℝ)..1, f t with hc
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (f t - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have he : (∫ t in (0:ℝ)..1, (f t - c) ^ 2) =
      (∫ t in (0:ℝ)..1, (f t) ^ 2) - 2 * c * c + c ^ 2 := by
    have hid : (fun t => (f t - c) ^ 2) = fun t => ((f t) ^ 2 - 2 * c * f t) + c ^ 2 := by
      funext t
      ring
    rw [hid, intervalIntegral.integral_add (hf2.sub (hf1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, ← hc]
    simp
  nlinarith

/-! ### The segment formula -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `u` of class C1 on an open ball and `x, y` in it:
`(u x - u y)^2 <= |x - y|^2 * int_0^1 |Du ((1 - t) y + t x)|^2 dt`. -/
theorem sq_sub_le_segment_integral {u : E → ℝ} {a : E} {r : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball a r)) {x y : E} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    (u x - u y) ^ 2 ≤
      ‖x - y‖ ^ 2 * ∫ t in (0:ℝ)..1, ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2 := by
  set γ : ℝ → E := fun t => (1 - t) • y + t • x with hγdef
  have hγ : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ ball a r := fun t ht =>
    convex_ball a r hy hx (by linarith [ht.2]) ht.1 (by ring)
  have hγd : ∀ t : ℝ, HasDerivAt γ (x - y) t := by
    intro t
    have h := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const y).add
      ((hasDerivAt_id t).smul_const x)
    have he : ((0:ℝ) - 1) • y + (1:ℝ) • x = x - y := by
      rw [zero_sub, neg_smul, one_smul, one_smul]
      abel
    rw [he] at h
    exact h
  have hγc : Continuous γ := by fun_prop
  have hfd : ContinuousOn (fderiv ℝ u) (ball a r) :=
    hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hdiff : ∀ z ∈ ball a r, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
    ((hu.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt le_rfl).hasFDerivAt
  have hDc : ContinuousOn (fun t => fderiv ℝ u (γ t)) (Icc (0:ℝ) 1) :=
    hfd.comp hγc.continuousOn hγ
  have hφc : ContinuousOn (fun t => fderiv ℝ u (γ t) (x - y)) (Icc (0:ℝ) 1) :=
    hDc.clm_apply continuousOn_const
  have hnc : ContinuousOn (fun t => ‖fderiv ℝ u (γ t)‖ ^ 2) (Icc (0:ℝ) 1) := hDc.norm.pow 2
  have hφ : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (u ∘ γ) (fderiv ℝ u (γ t) (x - y)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hdiff _ (hγ t ht)).comp_hasDerivAt t (hγd t)
  have hftc : (∫ t in (0:ℝ)..1, fderiv ℝ u (γ t) (x - y)) = u x - u y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hφ
      (hφc.intervalIntegrable_of_Icc zero_le_one)]
    simp [hγdef]
  have hcs := sq_unit_interval_integral_le hφc
  rw [hftc] at hcs
  refine hcs.trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((hφc.pow 2).intervalIntegrable_of_Icc zero_le_one)
    ((continuousOn_const.mul hnc).intervalIntegrable_of_Icc zero_le_one) ?_
  intro t _
  have h1 : |fderiv ℝ u (γ t) (x - y)| ≤ ‖fderiv ℝ u (γ t)‖ * ‖x - y‖ := by
    rw [← Real.norm_eq_abs]
    exact (fderiv ℝ u (γ t)).le_opNorm (x - y)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs] at h2
  calc (fderiv ℝ u (γ t) (x - y)) ^ 2 ≤ (‖fderiv ℝ u (γ t)‖ * ‖x - y‖) ^ 2 := h2
    _ = ‖x - y‖ ^ 2 * ‖fderiv ℝ u (γ t)‖ ^ 2 := by ring

/-- The segment formula in extended nonnegative reals, with the Lebesgue
integral over `[0, 1]`. -/
theorem ofReal_sq_sub_le_segment_lintegral {u : E → ℝ} {a : E} {r : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball a r)) {x y : E} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    ENNReal.ofReal ((u x - u y) ^ 2) ≤
      ENNReal.ofReal (‖x - y‖ ^ 2) *
        ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) := by
  have hγ : ∀ t ∈ Icc (0:ℝ) 1, (1 - t) • y + t • x ∈ ball a r := fun t ht =>
    convex_ball a r hy hx (by linarith [ht.2]) ht.1 (by ring)
  have hγc : Continuous (fun t : ℝ => (1 - t) • y + t • x) := by fun_prop
  have hnc : ContinuousOn (fun t : ℝ => ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) (Icc (0:ℝ) 1) :=
    (((hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hγc.continuousOn hγ).norm).pow 2
  have hint : IntegrableOn (fun t : ℝ => ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) (Ioc (0:ℝ) 1) :=
    hnc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := ENNReal.ofReal_le_ofReal (sq_sub_le_segment_integral hu hx hy)
  rw [ENNReal.ofReal_mul (sq_nonneg _), intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    at h
  exact h.trans (mul_le_mul_left' (lintegral_mono_set Ioc_subset_Icc_self) _)

end Segment

/-! ### Homotheties of a convex set and Haar measure -/

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Scaling of the Lebesgue integral under `z -> c z`, `c > 0`. -/
theorem haar_lintegral_comp_smul {G : E → ℝ≥0∞} (hG : Measurable G) {c : ℝ} (hc : 0 < c) :
    ∫⁻ z, G (c • z) ∂μ = ENNReal.ofReal ((c ^ finrank ℝ E)⁻¹) * ∫⁻ z, G z ∂μ := by
  have hm : Measurable (fun z : E => c • z) := measurable_const_smul c
  rw [← lintegral_map hG hm, Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr (pow_pos hc _)), smul_eq_mul]

/-- A homothety of ratio `c >= 1/2` centred at a point `p` of a convex set
`B` maps `B` into `B` and shrinks Haar measure by at most `2^n`:
`int_B G (c z + (1 - c) p) dz <= 2^n int_B G`. -/
theorem haar_lintegral_convex_homothety_le {B : Set E} (hB : Convex ℝ B)
    (hBm : MeasurableSet B) {G : E → ℝ≥0∞} (hG : Measurable G) {c d : ℝ} (hc : 1 / 2 ≤ c)
    (hd : 0 ≤ d) (hcd : c + d = 1) {p : E} (hp : p ∈ B) :
    ∫⁻ z in B, G (c • z + d • p) ∂μ ≤ 2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ := by
  have hc0 : 0 < c := by linarith
  have hGi : Measurable (B.indicator G) := hG.indicator hBm
  have hconst : ENNReal.ofReal ((c ^ finrank ℝ E)⁻¹) ≤ 2 ^ finrank ℝ E := by
    have h1 : (c ^ finrank ℝ E)⁻¹ ≤ (2:ℝ) ^ finrank ℝ E := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hc0.le)
        (by rw [inv_le_comm₀ hc0 two_pos]; linarith) _
    calc ENNReal.ofReal ((c ^ finrank ℝ E)⁻¹) ≤ ENNReal.ofReal ((2:ℝ) ^ finrank ℝ E) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 ^ finrank ℝ E := by rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  calc ∫⁻ z in B, G (c • z + d • p) ∂μ
      ≤ ∫⁻ z in B, B.indicator G (c • z + d • p) ∂μ := by
        refine setLIntegral_mono' hBm fun z hz => ?_
        rw [indicator_of_mem (hB hz hp hc0.le hd hcd)]
    _ ≤ ∫⁻ z, B.indicator G (c • z + d • p) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, B.indicator G (c • (z + c⁻¹ • d • p)) ∂μ := by
        congr 1
        funext z
        rw [smul_add, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
    _ = ∫⁻ z, B.indicator G (c • z) ∂μ :=
        lintegral_add_right_eq_self (fun z => B.indicator G (c • z)) _
    _ = ENNReal.ofReal ((c ^ finrank ℝ E)⁻¹) * ∫⁻ z, B.indicator G z ∂μ :=
        haar_lintegral_comp_smul μ hGi hc0
    _ ≤ 2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ := by
        rw [lintegral_indicator hBm]
        exact mul_le_mul_right' hconst _

/-! ### The triple integral -/

omit [BorelSpace E] in
/-- Tonelli in the two inner variables and a bound of the innermost integral
that is uniform in the other two variables. -/
theorem haar_triple_lintegral_le {B : Set E} (hBm : MeasurableSet B) {T : Set ℝ}
    (hTm : MeasurableSet T) (F : E → E → ℝ → ℝ≥0∞)
    (hF : Measurable (fun q : (E × E) × ℝ => F q.1.1 q.1.2 q.2)) {C : ℝ≥0∞}
    (hb : ∀ p ∈ B, ∀ t ∈ T, ∫⁻ z in B, F z p t ∂μ ≤ C) :
    ∫⁻ p in B, ∫⁻ z in B, ∫⁻ t in T, F z p t ∂volume ∂μ ∂μ ≤ μ B * (volume T * C) := by
  have hinner : ∀ p ∈ B, ∫⁻ z in B, ∫⁻ t in T, F z p t ∂volume ∂μ ≤ volume T * C := by
    intro p hp
    have hm : Measurable (Function.uncurry fun (z : E) (t : ℝ) => F z p t) :=
      hF.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc ∫⁻ t in T, ∫⁻ z in B, F z p t ∂μ ≤ ∫⁻ _ in T, C :=
          setLIntegral_mono' hTm fun t ht => hb p hp t ht
      _ = volume T * C := by rw [setLIntegral_const, mul_comm]
  calc ∫⁻ p in B, ∫⁻ z in B, ∫⁻ t in T, F z p t ∂volume ∂μ ∂μ ≤ ∫⁻ _ in B, volume T * C ∂μ :=
        setLIntegral_mono' hBm hinner
    _ = μ B * (volume T * C) := by rw [setLIntegral_const, mul_comm]

/-- The double integral over a convex set of the segment averages of `G` is
at most `2^n |B| int_B G`. -/
theorem haar_segment_average_le {B : Set E} (hB : Convex ℝ B) (hBm : MeasurableSet B)
    {G : E → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in B, ∫⁻ x in B, ∫⁻ t in Icc (0:ℝ) 1, G ((1 - t) • y + t • x) ∂volume ∂μ ∂μ ≤
      2 ^ finrank ℝ E * μ B * ∫⁻ z in B, G z ∂μ := by
  -- measurability of the integrand in all three variables, in both orders
  have hm2 : Measurable (fun q : (E × E) × ℝ => G ((1 - q.2) • q.1.2 + q.2 • q.1.1)) :=
    hG.comp (by fun_prop)
  have hm1 : Measurable (fun q : (E × E) × ℝ => G ((1 - q.2) • q.1.1 + q.2 • q.1.2)) :=
    hG.comp (by fun_prop)
  -- the two halves of the parameter interval
  set H1 : E → E → ℝ≥0∞ := fun x y => ∫⁻ t in Icc (0:ℝ) (1 / 2), G ((1 - t) • y + t • x)
    with hH1
  set H2 : E → E → ℝ≥0∞ := fun x y => ∫⁻ t in Icc (1 / 2 : ℝ) 1, G ((1 - t) • y + t • x)
    with hH2
  have hH1m : Measurable (fun q : E × E => H1 q.2 q.1) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Icc (0:ℝ) (1 / 2))) hm1
  have hH1x : ∀ y, Measurable (fun x => H1 x y) := fun y =>
    hH1m.comp (measurable_const.prodMk measurable_id)
  have hH1y : Measurable (fun y => ∫⁻ x in B, H1 x y ∂μ) :=
    Measurable.lintegral_prod_right' (ν := μ.restrict B) hH1m
  have hsplit : ∀ x y, ∫⁻ t in Icc (0:ℝ) 1, G ((1 - t) • y + t • x) ≤ H1 x y + H2 x y := by
    intro x y
    have hsub : Icc (0:ℝ) 1 ⊆ Icc (0:ℝ) (1 / 2) ∪ Icc (1 / 2 : ℝ) 1 := by
      rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
  -- the half `t >= 1/2`: substitute in `x`
  have h2 : ∫⁻ y in B, ∫⁻ x in B, H2 x y ∂μ ∂μ ≤
      μ B * (volume (Icc (1 / 2 : ℝ) 1) * (2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ)) := by
    refine haar_triple_lintegral_le μ hBm measurableSet_Icc
      (fun z p t => G ((1 - t) • p + t • z)) hm2 ?_
    intro p hp t ht
    have h := haar_lintegral_convex_homothety_le μ hB hBm hG (c := t) (d := 1 - t) ht.1
      (by linarith [ht.2]) (by ring) hp
    simpa only [add_comm] using h
  -- the half `t <= 1/2`: exchange `x` and `y`, then substitute in `y`
  have h1 : ∫⁻ y in B, ∫⁻ x in B, H1 x y ∂μ ∂μ ≤
      μ B * (volume (Icc (0:ℝ) (1 / 2)) * (2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ)) := by
    rw [lintegral_lintegral_swap (f := fun y x => H1 x y) hH1m.aemeasurable]
    refine haar_triple_lintegral_le μ hBm measurableSet_Icc
      (fun z p t => G ((1 - t) • z + t • p)) hm1 ?_
    intro p hp t ht
    exact haar_lintegral_convex_homothety_le μ hB hBm hG (c := 1 - t) (d := t)
      (by linarith [ht.2]) ht.1 (by ring) hp
  have hv1 : volume (Icc (0:ℝ) (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    rw [Real.volume_Icc]
    norm_num
  have hv2 : volume (Icc (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 / 2) := by
    rw [Real.volume_Icc]
    norm_num
  have hhalf : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  calc ∫⁻ y in B, ∫⁻ x in B, ∫⁻ t in Icc (0:ℝ) 1, G ((1 - t) • y + t • x) ∂volume ∂μ ∂μ
      ≤ ∫⁻ y in B, ∫⁻ x in B, (H1 x y + H2 x y) ∂μ ∂μ :=
        lintegral_mono fun y => lintegral_mono fun x => hsplit x y
    _ = ∫⁻ y in B, (∫⁻ x in B, H1 x y ∂μ + ∫⁻ x in B, H2 x y ∂μ) ∂μ := by
        congr 1
        funext y
        exact lintegral_add_left (hH1x y) _
    _ = ∫⁻ y in B, ∫⁻ x in B, H1 x y ∂μ ∂μ + ∫⁻ y in B, ∫⁻ x in B, H2 x y ∂μ ∂μ :=
        lintegral_add_left hH1y _
    _ ≤ μ B * (ENNReal.ofReal (1 / 2) * (2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ)) +
          μ B * (ENNReal.ofReal (1 / 2) * (2 ^ finrank ℝ E * ∫⁻ z in B, G z ∂μ)) := by
        rw [hv1] at h1
        rw [hv2] at h2
        exact add_le_add h1 h2
    _ = (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) *
          (2 ^ finrank ℝ E * μ B * ∫⁻ z in B, G z ∂μ) := by ring
    _ = 2 ^ finrank ℝ E * μ B * ∫⁻ z in B, G z ∂μ := by rw [hhalf, one_mul]

/-! ### The Poincare inequality on balls -/

/-- **Poincare inequality for Haar measure on balls**, in every
finite-dimensional real normed space: variance at most
`2^(n + 2) r^2` times the energy over the same ball, for tests C1 on the
closed ball. Every centre and every real radius. -/
theorem haar_poincareAt_ball (a : E) (r : ℝ) :
    poincareAt μ (fun _ => 1) (2 ^ (finrank ℝ E + 2)) 1 a r := by
  rcases le_or_gt r 0 with hr | hr
  · exact poincareAt_of_nonpos μ _ _ 1 a hr
  intro u hu
  rw [one_mul] at hu ⊢
  have huo : ContDiffOn ℝ 1 u (ball a r) := hu.mono ball_subset_closedBall
  have hB0 : μ (ball a r) ≠ 0 := (measure_ball_pos μ a hr).ne'
  have hBtop : μ (ball a r) ≠ ⊤ := measure_ball_lt_top.ne
  have hG : Measurable (fun z : E => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)) :=
    ((measurable_fderiv ℝ u).norm.pow_const 2).ennreal_ofReal
  have hpt : ∀ y ∈ ball a r,
      weightedVariance (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u ≤
        ∫⁻ x in ball a r, ENNReal.ofReal ((2 * r) ^ 2) *
          ∫⁻ t in Icc (0:ℝ) 1,
            ENNReal.ofReal (‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) ∂volume ∂μ := by
    intro y hy
    refine (iInf_le _ (u y)).trans (setLIntegral_mono' measurableSet_ball fun x hx => ?_)
    rw [ENNReal.ofReal_one, mul_one]
    refine (ofReal_sq_sub_le_segment_lintegral huo hx hy).trans (mul_le_mul_right' ?_ _)
    have hd : ‖x - y‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      have h1 := dist_triangle_right x y a
      rw [mem_ball] at hx hy
      linarith
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hd 2)
  have hE : weightedEnergy (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u =
      ∫⁻ z in ball a r, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) ∂μ := by
    unfold weightedEnergy
    simp only [ENNReal.ofReal_one, mul_one]
  have h4 : ENNReal.ofReal ((2 * r) ^ 2) = 4 * ENNReal.ofReal (r ^ 2) := by
    rw [mul_pow, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hmain : μ (ball a r) *
      weightedVariance (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u ≤
      μ (ball a r) * ((2 ^ (finrank ℝ E + 2) * ENNReal.ofReal (r ^ 2)) *
        weightedEnergy (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u) := by
    calc μ (ball a r) * weightedVariance (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u
        = ∫⁻ _ in ball a r,
            weightedVariance (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in ball a r, ∫⁻ x in ball a r, ENNReal.ofReal ((2 * r) ^ 2) *
            ∫⁻ t in Icc (0:ℝ) 1,
              ENNReal.ofReal (‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) ∂volume ∂μ ∂μ :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ((2 * r) ^ 2) * ∫⁻ y in ball a r, ∫⁻ x in ball a r,
            ∫⁻ t in Icc (0:ℝ) 1,
              ENNReal.ofReal (‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2) ∂volume ∂μ ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          funext y
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((2 * r) ^ 2) * (2 ^ finrank ℝ E * μ (ball a r) *
            ∫⁻ z in ball a r, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) ∂μ) :=
          mul_le_mul_left' (haar_segment_average_le μ (convex_ball a r) measurableSet_ball hG) _
      _ = μ (ball a r) * ((2 ^ (finrank ℝ E + 2) * ENNReal.ofReal (r ^ 2)) *
            weightedEnergy (μ.restrict (ball a r)) (fun _ => ENNReal.ofReal 1) u) := by
          rw [hE, h4]
          ring
  exact (ENNReal.mul_le_mul_left hB0 hBtop).mp hmain

/-- The Poincare inequality for Haar measure at all balls, with the finite
constant `2^(n + 2)`. -/
theorem haar_poincare_all_balls :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : E) (r : ℝ), 0 < r → poincareAt μ (fun _ => 1) P 1 a r :=
  ⟨2 ^ (finrank ℝ E + 2), ENNReal.pow_ne_top ENNReal.ofNat_ne_top,
    fun a r _ => haar_poincareAt_ball μ a r⟩

/-- The same inequality in the form `ballPoincare`: on the left the integral
of the squared deviation from the mean over the ball. -/
theorem haar_ballPoincare : ballPoincare μ (fun _ => 1) (2 ^ (finrank ℝ E + 2)) :=
  (poincareAt_one_iff_ballPoincare μ continuous_const (fun _ => zero_le_one) _).mp
    fun a r _ => haar_poincareAt_ball μ a r

end Haar

/-! ### Euclidean spaces and premise P0 -/

/-- Lebesgue measure on `EuclideanSpace R (Fin n)`: Poincare on every ball
with constant `2^(n + 2)`. -/
theorem lebesgue_poincareAt_euclidean (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    poincareAt (volume : Measure (EuclideanSpace ℝ (Fin n))) (fun _ => 1) (2 ^ (n + 2)) 1 a r := by
  have h := haar_poincareAt_ball (volume : Measure (EuclideanSpace ℝ (Fin n))) a r
  rwa [finrank_euclideanSpace_fin] at h

/-- Three-space: constant `32`. -/
theorem lebesgue_poincareAt_three (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    poincareAt (volume : Measure (EuclideanSpace ℝ (Fin 3))) (fun _ => 1) 32 1 a r := by
  have h := lebesgue_poincareAt_euclidean 3 a r
  norm_num at h
  exact h

/-- Three-space, variance about the mean: `ballPoincare` with constant `32`. -/
theorem lebesgue_ballPoincare_three :
    ballPoincare (volume : Measure (EuclideanSpace ℝ (Fin 3))) (fun _ => 1) 32 :=
  (poincareAt_one_iff_ballPoincare volume continuous_const (fun _ => zero_le_one) _).mp
    fun a r _ => lebesgue_poincareAt_three a r

/-- **Premise P0 holds**, with `P = 32`. -/
theorem lebesguePoincarePremise_holds : LebesguePoincarePremise :=
  ⟨32, by norm_num, fun a r _ => lebesgue_poincareAt_three a r⟩

/-! ### The statements of `DoublingPoincare`, `LatticeSmallBalls` and `LatticeDP` without P0

Each theorem below is an existing theorem applied to
`lebesguePoincarePremise_holds`. The suffix of its name lists the premises
that remain as hypotheses. -/

/-- A weight between `m > 0` and `M` on a ball satisfies the strong Poincare
inequality at that ball with constant `32 M / m`. No premise. -/
theorem poincareAt_of_bounds_three {w : LatticeSpace → ℝ} {m M : ℝ} (hm : 0 < m)
    {a : LatticeSpace} {r : ℝ} (hb : ∀ x ∈ ball a r, m ≤ w x ∧ w x ≤ M) :
    poincareAt (volume : Measure LatticeSpace) w (ENNReal.ofReal (M / m) * 32) 1 a r := by
  refine poincareAt_of_bounds hm le_rfl ?_ (lebesgue_poincareAt_three a r)
  intro x hx
  rw [one_mul] at hx
  exact hb x hx

/-- Small balls, strong Poincare; `lem:circle` remains. -/
theorem lattice_small_ball_poincare_modulo_circle {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
      rho ≤ Real.sqrt (1 + ‖x0‖) / 10 →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 x0 rho :=
  lattice_small_ball_poincare halpha lebesguePoincarePremise_holds hcircle

/-- Large balls, weak Poincare (energy over the 4-fold ball); `lem:circle`
remains. -/
theorem lattice_large_ball_weak_poincare_modulo_circle {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ),
      Real.sqrt (1 + ‖x0‖) / 10 ≤ rho →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        K 4 x0 rho :=
  lattice_large_ball_weak_poincare halpha lebesguePoincarePremise_holds hcircle

/-- Weak Poincare at all balls; `lem:circle` remains. -/
theorem lattice_weak_poincare_all_modulo_circle {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 4 a r :=
  lattice_weak_poincare_all halpha lebesguePoincarePremise_holds hcircle

/-- **`thm:B`(a)**: doubling and the strong Poincare inequality at all balls,
for every `alpha >= 0`; `lem:circle` and the self-improvement remain. -/
theorem theorem_B_a_modulo_circle_and_self_improvement {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) (hself : SelfImprovementPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 a r) :=
  theorem_B_a_modulo_premises halpha lebesguePoincarePremise_holds hcircle hself

/-- `thm:B`(a) with the Poincare inequality in the form `ballPoincare`;
`lem:circle` and the self-improvement remain. -/
theorem theorem_B_a_ball_poincare_modulo_circle_and_self_improvement {alpha : ℝ}
    (halpha : 0 ≤ alpha) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ballPoincare (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) P) :=
  theorem_B_a_ball_poincare_modulo_premises halpha lebesguePoincarePremise_holds hcircle hself

/-- **`thm:B`, conclusion**, for `alpha >= 4`: the lattice weight and its
Gaussian marginal are not parabolic; `lem:circle`, the self-improvement and
the volume criterion remain. -/
theorem theorem_B_modulo_circle_self_improvement_and_volume {alpha : ℝ≥0}
    (halpha : 4 ≤ (alpha : ℝ)) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) (hvol : VolumeCriterionPremise) :
    ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
    ¬ parabolic (volume : Measure LatticeSpace)
      (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha)) :=
  theorem_B_modulo_premises halpha lebesguePoincarePremise_holds hcircle hself hvol

/-- **`thm:B`, all parts**, for `alpha >= 4`; `lem:circle`, the
self-improvement and the volume criterion remain. -/
theorem theorem_B_statement_modulo_circle_self_improvement_and_volume {alpha : ℝ≥0}
    (halpha : 4 ≤ (alpha : ℝ)) (hcircle : CircleLemmaPremise alpha)
    (hself : SelfImprovementPremise) (hvol : VolumeCriterionPremise) :
    ((∃ D : ℝ≥0∞, D ≠ ⊤ ∧
        doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
      (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
        poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
          P 1 a r)) ∧
    (¬ sphereTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ rayTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ volumeTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 64 ≤ r →
      c * r^3 ≤ weightedBallVolume volume (latticeWeight latticeValleys alpha) r ∧
      weightedBallVolume volume (latticeWeight latticeValleys alpha) r ≤
        (4/3) * Real.pi * r^3) ∧
    (¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
      ¬ parabolic (volume : Measure LatticeSpace)
        (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha))) :=
  theorem_B_statement_modulo_premises halpha lebesguePoincarePremise_holds hcircle hself hvol

end BrownRadial
