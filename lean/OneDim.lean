import Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
The quantitative claim of `lem:1d`: a continuous positive weight on the real
line that is doubling on intervals and satisfies the interval Poincare
inequality for C1 test functions has
`mu([-r,r]) * nu([-r,r]) <= 32 * C * D^3 * r^2`, with `nu = dt / v`.

The paper's extremal test function is only piecewise C1 (its derivative jumps
at `-r` and `r`), so it is not an admissible C1 test. The proof here composes
the normalized resistance primitive with a C1 step whose derivative is a
continuous trapezoid, and lets the trapezoid tend to the indicator of `[0,1]`.
This recovers the constant 32 exactly using C1 tests only.
-/

open MeasureTheory Set
namespace BrownRadial

theorem interval_mass_mono {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    (∫ t in a..b, v t) ≤ ∫ t in c..d, v t :=
  intervalIntegral.integral_mono_interval hca hab hbd
    (Filter.Eventually.of_forall fun t => (hpos t).le) (hv.intervalIntegrable _ _)

theorem interval_mass_pos {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    {a b : ℝ} (hab : a < b) : 0 < ∫ t in a..b, v t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hv.intervalIntegrable _ _)
    (fun t _ => hpos t) hab

/-- The doubling constant of a positive weight is positive. -/
theorem doubling_constant_pos {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t) {D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t) : 0 < D := by
  have h := hdoubling 0 1 zero_lt_one
  have h1 : 0 < ∫ t in (0 - 2*1 : ℝ)..(0 + 2*1), v t := interval_mass_pos hv hpos (by norm_num)
  have h2 : 0 < ∫ t in (0 - 1 : ℝ)..(0 + 1), v t := interval_mass_pos hv hpos (by norm_num)
  by_contra hD
  push_neg at hD
  nlinarith [mul_nonneg (neg_nonneg.mpr hD) h2.le]

/-- Three applications of doubling: the eightfold concentric dilate. -/
theorem doubling_three {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t) {D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t)
    (c h : ℝ) (hh : 0 < h) :
    (∫ t in (c - 8*h)..(c + 8*h), v t) ≤ D^3 * ∫ t in (c - h)..(c + h), v t := by
  have hD := doubling_constant_pos hv hpos hdoubling
  have h1 := hdoubling c h hh
  have h2 := hdoubling c (2*h) (by positivity)
  have h3 := hdoubling c (4*h) (by positivity)
  rw [show c - 2*(2*h) = c - 4*h by ring, show c + 2*(2*h) = c + 4*h by ring] at h2
  rw [show c - 2*(4*h) = c - 8*h by ring, show c + 2*(4*h) = c + 8*h by ring] at h3
  calc
    (∫ t in (c - 8*h)..(c + 8*h), v t) ≤ D * ∫ t in (c - 4*h)..(c + 4*h), v t := h3
    _ ≤ D * (D * ∫ t in (c - 2*h)..(c + 2*h), v t) := mul_le_mul_of_nonneg_left h2 hD.le
    _ ≤ D * (D * (D * ∫ t in (c - h)..(c + h), v t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hD.le) hD.le
    _ = D^3 * ∫ t in (c - h)..(c + h), v t := by ring

/-- `[-r,r]` lies in the eightfold dilate of `[r,2r]`. -/
theorem center_mass_le_right {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t) {D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (-r)..r, v t) ≤ D^3 * ∫ t in r..(2*r), v t := by
  have h := doubling_three hv hpos hdoubling (3*r/2) (r/2) (by positivity)
  rw [show 3*r/2 - r/2 = r by ring, show 3*r/2 + r/2 = 2*r by ring] at h
  exact (interval_mass_mono hv hpos (by linarith) (by linarith) (by linarith)).trans h

/-- `[-r,r]` lies in the eightfold dilate of `[-2r,-r]`. -/
theorem center_mass_le_left {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t) {D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (-r)..r, v t) ≤ D^3 * ∫ t in (-(2*r))..(-r), v t := by
  have h := doubling_three hv hpos hdoubling (-(3*r/2)) (r/2) (by positivity)
  rw [show -(3*r/2) - r/2 = -(2*r) by ring, show -(3*r/2) + r/2 = -r by ring] at h
  exact (interval_mass_mono hv hpos (by linarith) (by linarith) (by linarith)).trans h

theorem profile_integral_nonpos_zero {f : ℝ → ℝ} (h0 : ∀ s, s ≤ 0 → f s = 0)
    {A : ℝ} (hA : A ≤ 0) : (∫ x in (0:ℝ)..A, f x) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
  · simp
  · intro x hx
    rw [uIcc_of_ge hA] at hx
    exact h0 x hx.2

theorem profile_integral_tail_zero {f : ℝ → ℝ} (h1 : ∀ s, 1 ≤ s → f s = 0)
    {B : ℝ} (hB : 1 ≤ B) : (∫ x in (1:ℝ)..B, f x) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
  · simp
  · intro x hx
    rw [uIcc_of_le hB] at hx
    exact h1 x hx.1

/-- A continuous function vanishing off `[0,1]` has the same integral over
every interval containing `[0,1]`. -/
theorem integral_unit_support {g : ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ s, s ≤ 0 → g s = 0) (h1 : ∀ s, 1 ≤ s → g s = 0)
    {A B : ℝ} (hA : A ≤ 0) (hB : 1 ≤ B) :
    (∫ s in A..B, g s) = ∫ s in (0:ℝ)..1, g s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable A 0) (hg.intervalIntegrable 0 B),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 1) (hg.intervalIntegrable 1 B),
    profile_integral_tail_zero h1 hB, intervalIntegral.integral_symm 0 A,
    profile_integral_nonpos_zero h0 hA]
  simp

/-- Resistance of the weight measured from `-r`. -/
noncomputable def resistancePrimitive (v : ℝ → ℝ) (r t : ℝ) : ℝ := ∫ x in (-r)..t, 1 / v x

theorem inv_weight_continuous {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t) :
    Continuous (fun x => 1 / v x) :=
  continuous_const.div hv (fun t => (hpos t).ne')

theorem resistancePrimitive_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (r t : ℝ) : HasDerivAt (resistancePrimitive v r) (1 / v t) t :=
  ((inv_weight_continuous hv hpos).integral_hasStrictDerivAt (-r) t).hasDerivAt

theorem resistancePrimitive_self_pos {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    {r : ℝ} (hr : 0 < r) : 0 < resistancePrimitive v r r := by
  unfold resistancePrimitive
  exact interval_mass_pos (inv_weight_continuous hv hpos)
    (fun x => one_div_pos.mpr (hpos x)) (by linarith)

theorem resistancePrimitive_nonpos {v : ℝ → ℝ} (hpos : ∀ t, 0 < v t)
    {r t : ℝ} (ht : t ≤ -r) : resistancePrimitive v r t ≤ 0 := by
  unfold resistancePrimitive
  rw [intervalIntegral.integral_symm t (-r)]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg ht
    (fun x _ => (one_div_pos.mpr (hpos x)).le))

theorem resistancePrimitive_ge {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    {r t : ℝ} (hr : 0 ≤ r) (ht : r ≤ t) :
    resistancePrimitive v r r ≤ resistancePrimitive v r t := by
  unfold resistancePrimitive
  exact interval_mass_mono (inv_weight_continuous hv hpos)
    (fun x => one_div_pos.mpr (hpos x)) le_rfl (by linarith) ht

/-- The C1 test function: a step profile composed with the normalized
resistance primitive. -/
noncomputable def profileTest (v f : ℝ → ℝ) (r t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..(resistancePrimitive v r t / resistancePrimitive v r r), f x

theorem profileTest_hasDerivAt {v f : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (hf : Continuous f) (r t : ℝ) :
    HasDerivAt (profileTest v f r)
      (f (resistancePrimitive v r t / resistancePrimitive v r r) *
        (1 / v t / resistancePrimitive v r r)) t := by
  have hq : HasDerivAt (fun t => resistancePrimitive v r t / resistancePrimitive v r r)
      (1 / v t / resistancePrimitive v r r) t :=
    (resistancePrimitive_hasDerivAt hv hpos r t).div_const _
  have hG : HasDerivAt (fun s => ∫ x in (0:ℝ)..s, f x)
      (f (resistancePrimitive v r t / resistancePrimitive v r r))
      (resistancePrimitive v r t / resistancePrimitive v r r) :=
    (hf.integral_hasStrictDerivAt 0 _).hasDerivAt
  exact hG.comp t hq

theorem profileTest_contDiff {v f : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (hf : Continuous f) (r : ℝ) : ContDiff ℝ 1 (profileTest v f r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (profileTest_hasDerivAt hv hpos hf r t).differentiableAt, ?_⟩
  have hd : deriv (profileTest v f r) = fun t =>
      f (resistancePrimitive v r t / resistancePrimitive v r r) *
        (1 / v t / resistancePrimitive v r r) :=
    funext fun t => (profileTest_hasDerivAt hv hpos hf r t).deriv
  rw [hd]
  have hQ : Continuous (resistancePrimitive v r) :=
    continuous_iff_continuousAt.mpr fun t => (resistancePrimitive_hasDerivAt hv hpos r t).continuousAt
  exact (hf.comp (hQ.div_const _)).mul ((inv_weight_continuous hv hpos).div_const _)

theorem profileTest_left {v f : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (h0 : ∀ s, s ≤ 0 → f s = 0) {r t : ℝ} (hr : 0 < r) (ht : t ≤ -r) :
    profileTest v f r t = 0 := by
  unfold profileTest
  exact profile_integral_nonpos_zero h0 (div_nonpos_of_nonpos_of_nonneg
    (resistancePrimitive_nonpos hpos ht) (resistancePrimitive_self_pos hv hpos hr).le)

theorem profileTest_right {v f : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (hf : Continuous f) (h1 : ∀ s, 1 ≤ s → f s = 0) {r t : ℝ} (hr : 0 < r) (ht : r ≤ t) :
    profileTest v f r t = ∫ x in (0:ℝ)..1, f x := by
  unfold profileTest
  have hq : 1 ≤ resistancePrimitive v r t / resistancePrimitive v r r := by
    rw [le_div_iff₀ (resistancePrimitive_self_pos hv hpos hr), one_mul]
    exact resistancePrimitive_ge hv hpos hr.le ht
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 _),
    profile_integral_tail_zero h1 hq, add_zero]

/-- Energy of the test function on `[-2r,2r]`, by the substitution
`s = resistancePrimitive t / resistancePrimitive r`. -/
theorem profileTest_energy {v f : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (hf : Continuous f) (h0 : ∀ s, s ≤ 0 → f s = 0) (h1 : ∀ s, 1 ≤ s → f s = 0)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (-(2*r))..(2*r), (deriv (profileTest v f r) t)^2 * v t) =
      (1 / resistancePrimitive v r r) * ∫ s in (0:ℝ)..1, (f s)^2 := by
  have hN : 0 < resistancePrimitive v r r := resistancePrimitive_self_pos hv hpos hr
  have hpt : (fun t => (deriv (profileTest v f r) t)^2 * v t) = fun t =>
      (1 / resistancePrimitive v r r) *
        (((fun s => (f s)^2) ∘ (fun t => resistancePrimitive v r t / resistancePrimitive v r r)) t *
          (1 / v t / resistancePrimitive v r r)) := by
    funext t
    rw [(profileTest_hasDerivAt hv hpos hf r t).deriv]
    have hvt := (hpos t).ne'
    have hN' := hN.ne'
    simp only [Function.comp_apply]
    field_simp
  rw [hpt, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_deriv
    (fun t _ => (resistancePrimitive_hasDerivAt hv hpos r t).div_const (resistancePrimitive v r r))
    ((inv_weight_continuous hv hpos).div_const (resistancePrimitive v r r)).continuousOn
    (hf.pow 2)]
  congr 1
  apply integral_unit_support (hf.pow 2)
  · intro s hs
    simp [h0 s hs]
  · intro s hs
    simp [h1 s hs]
  · exact div_nonpos_of_nonpos_of_nonneg (resistancePrimitive_nonpos hpos (by linarith)) hN.le
  · rw [le_div_iff₀ hN, one_mul]
    exact resistancePrimitive_ge hv hpos hr.le (by linarith)

/-- A function equal to `0` on the left third and to `K` on the right third
has weighted second moment about any constant at least the two plateau terms. -/
theorem two_plateau_variance {v u : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    (hu : Continuous u) {r K : ℝ} (hr : 0 < r)
    (hleft : ∀ t, t ≤ -r → u t = 0) (hright : ∀ t, r ≤ t → u t = K) (m : ℝ) :
    (∫ t in (-(2*r))..(-r), v t) * m^2 + (∫ t in r..(2*r), v t) * (K - m)^2 ≤
      ∫ t in (-(2*r))..(2*r), (u t - m)^2 * v t := by
  have hc : Continuous (fun t => (u t - m)^2 * v t) := ((hu.sub continuous_const).pow 2).mul hv
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-(2*r)) (-r)) (hc.intervalIntegrable (-r) (2*r)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-r) r) (hc.intervalIntegrable r (2*r))]
  have hL : (∫ t in (-(2*r))..(-r), (u t - m)^2 * v t) =
      (∫ t in (-(2*r))..(-r), v t) * m^2 := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    show (u t - m)^2 * v t = v t * m^2
    rw [hleft t ht.2]
    ring
  have hR : (∫ t in r..(2*r), (u t - m)^2 * v t) = (∫ t in r..(2*r), v t) * (K - m)^2 := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    show (u t - m)^2 * v t = v t * (K - m)^2
    rw [hright t ht.1]
    ring
  have hM : 0 ≤ ∫ t in (-r)..r, (u t - m)^2 * v t :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun t _ => mul_nonneg (sq_nonneg _) (hpos t).le)
  rw [hL, hR]
  linarith

/-- Scalar bookkeeping of the proof of `lem:1d`. -/
theorem one_dimensional_A2_algebra {a b mass N K E C D r m V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hD : 0 < D)
    (hleft : mass ≤ D^3 * a) (hright : mass ≤ D^3 * b)
    (hvar : a * m^2 + b * (K - m)^2 ≤ V)
    (hP : V ≤ C * (2*r - -(2*r))^2 * (1 / N * E)) :
    mass * N * K^2 ≤ 32 * C * D^3 * r^2 * E := by
  have h1 : a*b*K^2 ≤ (a+b)*(a*m^2 + b*(K-m)^2) := by
    nlinarith [sq_nonneg (a*m - b*(K-m))]
  have h2 : mass*(a+b) ≤ 2*D^3*(a*b) := by
    nlinarith [mul_le_mul_of_nonneg_right hright ha.le, mul_le_mul_of_nonneg_right hleft hb.le]
  have h3 : mass*K^2 ≤ 2*D^3*(a*m^2 + b*(K-m)^2) := by
    have h : mass*K^2*(a+b) ≤ 2*D^3*(a*m^2 + b*(K-m)^2)*(a+b) := by
      calc
        mass*K^2*(a+b) = mass*(a+b)*K^2 := by ring
        _ ≤ 2*D^3*(a*b)*K^2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg K)
        _ = 2*D^3*(a*b*K^2) := by ring
        _ ≤ 2*D^3*((a+b)*(a*m^2 + b*(K-m)^2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2*D^3*(a*m^2 + b*(K-m)^2)*(a+b) := by ring
    exact le_of_mul_le_mul_right h (by linarith)
  have h4 : mass*K^2 ≤ 2*D^3*(C * (2*r - -(2*r))^2 * (1 / N * E)) :=
    h3.trans (mul_le_mul_of_nonneg_left (hvar.trans hP) (by positivity))
  have h5 := mul_le_mul_of_nonneg_right h4 hN.le
  have h6 : 2*D^3*(C * (2*r - -(2*r))^2 * (1 / N * E))*N = 32*C*D^3*r^2*E := by
    field_simp
    ring
  calc
    mass*N*K^2 = mass*K^2*N := by ring
    _ ≤ 2*D^3*(C * (2*r - -(2*r))^2 * (1 / N * E))*N := h5
    _ = 32*C*D^3*r^2*E := h6

/-- The inequality of `lem:1d` for an arbitrary continuous step derivative
`f` supported in `[0,1]`: the constant is `32` times the ratio of the energy of
`f` to the square of its mass. -/
theorem one_dimensional_A2_profile {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ t, 0 < v t)
    {C D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t)
    (hpoincare : ∀ a b : ℝ, a < b → ∀ u : ℝ → ℝ, ContDiff ℝ 1 u → ∀ m : ℝ,
      m = (∫ t in a..b, u t * v t) / (∫ t in a..b, v t) →
      (∫ t in a..b, (u t - m)^2 * v t) ≤ C * (b - a)^2 * ∫ t in a..b, (deriv u t)^2 * v t)
    {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ s, s ≤ 0 → f s = 0) (h1 : ∀ s, 1 ≤ s → f s = 0) :
    (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) * (∫ s in (0:ℝ)..1, f s)^2 ≤
      32 * C * D^3 * r^2 * ∫ s in (0:ℝ)..1, (f s)^2 := by
  have hD := doubling_constant_pos hv hpos hdoubling
  have hN : 0 < resistancePrimitive v r r := resistancePrimitive_self_pos hv hpos hr
  have ha : 0 < ∫ t in (-(2*r))..(-r), v t := interval_mass_pos hv hpos (by linarith)
  have hb : 0 < ∫ t in r..(2*r), v t := interval_mass_pos hv hpos (by linarith)
  have hu := profileTest_contDiff hv hpos hf r
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∫ t in (-(2*r))..(2*r), profileTest v f r t * v t) /
      (∫ t in (-(2*r))..(2*r), v t) := ⟨_, rfl⟩
  have hP := hpoincare (-(2*r)) (2*r) (by linarith) (profileTest v f r) hu m hm
  rw [profileTest_energy hv hpos hf h0 h1 hr] at hP
  have hvar := two_plateau_variance hv hpos hu.continuous hr
    (fun t ht => profileTest_left hv hpos h0 hr ht)
    (fun t ht => profileTest_right hv hpos hf h1 hr ht) m
  exact one_dimensional_A2_algebra ha hb hN hD
    (center_mass_le_left hv hpos hdoubling hr) (center_mass_le_right hv hpos hdoubling hr)
    hvar hP

/-- Continuous trapezoid: zero off `[0,1]`, one on `[ε,1-ε]`. -/
noncomputable def trapezoidProfile (ε s : ℝ) : ℝ := max 0 (min (s/ε) (min 1 ((1 - s)/ε)))

theorem trapezoidProfile_continuous (ε : ℝ) : Continuous (trapezoidProfile ε) :=
  continuous_const.max ((continuous_id.div_const ε).min
    (continuous_const.min ((continuous_const.sub continuous_id).div_const ε)))

theorem trapezoidProfile_nonneg (ε s : ℝ) : 0 ≤ trapezoidProfile ε s := le_max_left _ _

theorem trapezoidProfile_le_one (ε s : ℝ) : trapezoidProfile ε s ≤ 1 :=
  max_le zero_le_one ((min_le_right _ _).trans (min_le_left _ _))

theorem trapezoidProfile_left {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ 0) :
    trapezoidProfile ε s = 0 :=
  max_eq_left ((min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg hs hε.le))

theorem trapezoidProfile_right {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 1 ≤ s) :
    trapezoidProfile ε s = 0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)))

theorem trapezoidProfile_plateau {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : ε ≤ s) (hs1 : s ≤ 1 - ε) :
    trapezoidProfile ε s = 1 := by
  have h1 : 1 ≤ s/ε := by rw [le_div_iff₀ hε]; linarith
  have h2 : 1 ≤ (1 - s)/ε := by rw [le_div_iff₀ hε]; linarith
  unfold trapezoidProfile
  rw [min_eq_left h2, min_eq_right h1]
  exact max_eq_right zero_le_one

theorem trapezoidProfile_mass_ge {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1/2) :
    1 - 2*ε ≤ ∫ s in (0:ℝ)..1, trapezoidProfile ε s := by
  have hmono : (∫ s in ε..(1 - ε), trapezoidProfile ε s) ≤ ∫ s in (0:ℝ)..1, trapezoidProfile ε s :=
    intervalIntegral.integral_mono_interval hε.le (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun s => trapezoidProfile_nonneg ε s)
      ((trapezoidProfile_continuous ε).intervalIntegrable _ _)
  have he : (∫ s in ε..(1 - ε), trapezoidProfile ε s) = 1 - 2*ε := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ))]
    · simp
      ring
    · intro s hs
      rw [uIcc_of_le (by linarith)] at hs
      exact trapezoidProfile_plateau hε hs.1 hs.2
  linarith

theorem trapezoidProfile_energy_le (ε : ℝ) :
    (∫ s in (0:ℝ)..1, (trapezoidProfile ε s)^2) ≤ ∫ s in (0:ℝ)..1, trapezoidProfile ε s := by
  apply intervalIntegral.integral_mono_on zero_le_one
    (((trapezoidProfile_continuous ε).pow 2).intervalIntegrable _ _)
    ((trapezoidProfile_continuous ε).intervalIntegrable _ _)
  intro s _
  nlinarith [trapezoidProfile_nonneg ε s, trapezoidProfile_le_one ε s]

/-- `lem:1d`, quantitative claim, with the paper's constant. The Poincare
hypothesis is required only for C1 test functions, centred at the actual
weighted mean on the interval. -/
theorem one_dimensional_doubling_poincare_A2 {v : ℝ → ℝ} (hv : Continuous v)
    (hpos : ∀ t, 0 < v t) {C D : ℝ}
    (hdoubling : ∀ c h : ℝ, 0 < h →
      (∫ t in (c - 2*h)..(c + 2*h), v t) ≤ D * ∫ t in (c - h)..(c + h), v t)
    (hpoincare : ∀ a b : ℝ, a < b → ∀ u : ℝ → ℝ, ContDiff ℝ 1 u → ∀ m : ℝ,
      m = (∫ t in a..b, u t * v t) / (∫ t in a..b, v t) →
      (∫ t in a..b, (u t - m)^2 * v t) ≤ C * (b - a)^2 * ∫ t in a..b, (deriv u t)^2 * v t)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) ≤ 32 * C * D^3 * r^2 := by
  have hmass : 0 < ∫ t in (-r)..r, v t := interval_mass_pos hv hpos (by linarith)
  have hres : 0 < ∫ t in (-r)..r, 1 / v t := resistancePrimitive_self_pos hv hpos hr
  have hprod := mul_pos hmass hres
  have key : ∀ ε : ℝ, 0 < ε → ε < 1/2 →
      (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) * (1 - 2*ε) ≤ 32 * C * D^3 * r^2 := by
    intro ε hε hε2
    have hK := trapezoidProfile_mass_ge hε hε2
    have hE := trapezoidProfile_energy_le ε
    have hE0 : 0 ≤ ∫ s in (0:ℝ)..1, (trapezoidProfile ε s)^2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
    have hmain := one_dimensional_A2_profile hv hpos hdoubling hpoincare hr
      (trapezoidProfile_continuous ε) (fun s hs => trapezoidProfile_left hε hs)
      (fun s hs => trapezoidProfile_right hε hs)
    have hKpos : 0 < ∫ s in (0:ℝ)..1, trapezoidProfile ε s := by linarith
    have hX : 0 ≤ 32 * C * D^3 * r^2 := by
      by_contra hneg
      push_neg at hneg
      have hlhs := mul_pos hprod (pow_pos hKpos 2)
      nlinarith [mul_nonneg (neg_nonneg.mpr hneg.le) hE0]
    have hstep : (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) *
        (∫ s in (0:ℝ)..1, trapezoidProfile ε s) ≤ 32 * C * D^3 * r^2 := by
      have h := hmain.trans (mul_le_mul_of_nonneg_left hE hX)
      have h' : (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) *
          (∫ s in (0:ℝ)..1, trapezoidProfile ε s) * (∫ s in (0:ℝ)..1, trapezoidProfile ε s) ≤
          32 * C * D^3 * r^2 * (∫ s in (0:ℝ)..1, trapezoidProfile ε s) := by
        calc
          _ = (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) *
              (∫ s in (0:ℝ)..1, trapezoidProfile ε s)^2 := by ring
          _ ≤ _ := h
      exact le_of_mul_le_mul_right h' hKpos
    exact (mul_le_mul_of_nonneg_left hK hprod.le).trans hstep
  have hquarter := key (1/4) (by norm_num) (by norm_num)
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (∫ t in (-r)..r, v t) * (∫ t in (-r)..r, 1 / v t) := ⟨_, rfl⟩
  rw [← hP] at hcon hquarter key hprod
  have hε0 : 0 < (P - 32 * C * D^3 * r^2) / (4*P) := div_pos (by linarith) (by linarith)
  have hε2 : (P - 32 * C * D^3 * r^2) / (4*P) < 1/2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have h := key _ hε0 hε2
  have he : P * (1 - 2*((P - 32 * C * D^3 * r^2) / (4*P))) = (P + 32 * C * D^3 * r^2)/2 := by
    field_simp
    ring
  rw [he] at h
  linarith

end BrownRadial
