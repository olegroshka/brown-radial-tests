import DoublingPoincare
import LatticeLocal

/-!
Small balls in the proof of `thm:B`(a) (paper, paragraph "Small balls"):
for the lattice weight `w`, every ball `B(x_0, rho)` with
`rho <= sigma_0 / 10`, `sigma_0^2 = 1 + |x_0|`, satisfies the strong Poincare
inequality and doubling, with constants that depend only on `alpha` and on
the constants of the two cited inputs.

The cases are those of the paper.

* Centre in `{|x| < 16}`: `33^(-alpha/2) <= w <= 1` on `2B`. This is proved
  for every radius up to 8, as the paper states it; a small ball centred
  there has radius at most `1/2`.
* Far case, `dist(x_0, Gamma) >= 2 rho`: `max_{2B} w <= 16^(alpha/2) min_B w`
  and `w` varies on `B` by a factor `9^(alpha/2)`.
* Near case, `dist(x_0, Gamma) <= 2 rho`, `|x_0| >= 16`: `(eq:wcompare)`, the
  comparison of `w` with `sigma_0^(-alpha) (1 + d_C^2)^(alpha/2)` for one
  lattice circle `C`, on `B`; on `2B` when `rho <= sigma_0 / 20`. For
  `sigma_0 / 20 < rho <= sigma_0 / 10` doubling comes from the mass bound
  `mu(B) >= c |B|`.

The theorems named `..._at` are statements about one ball: their hypotheses
are the Poincare inequality or doubling of the comparison weight (the constant
weight, the circle weights) at that same ball, with the same centre and the
same radius. The two final theorems take `LebesguePoincarePremise` and
`CircleLemmaPremise alpha` and nothing else. No cited result is proved here.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### Scalar facts and constants -/

/-- A small ball centred in `{|x| < 16}` has radius at most `1/2`
(`sigma_0 < 5`), well inside the paper's "radius at most 8". -/
theorem lattice_small_radius_le_half {x0 : LatticeSpace} (hx0 : ‖x0‖ < 16) {ρ : ℝ}
    (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10) : ρ ≤ 1 / 2 := by
  have h : Real.sqrt (1 + ‖x0‖) ≤ 5 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num
    linarith
  linarith

/-- Paper, last case of the doubling argument: a ball centred in shell
`k >= 4` with `sigma_0 / 20 < rho <= sigma_0 / 10` has radius in
`[s_k / 20, s_k]`, inside the range `[s_k / 32, s_k]` of the cell-mass
paragraph. -/
theorem lattice_small_mass_radius_range {k : ℕ} (hk : 4 ≤ k) {x0 : LatticeSpace}
    (h1 : (2:ℝ)^k ≤ ‖x0‖) (h2 : ‖x0‖ < (2:ℝ)^(k+1)) {ρ : ℝ}
    (hlo : Real.sqrt (1 + ‖x0‖) / 20 < ρ) (hhi : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10) :
    Real.sqrt ((2:ℝ)^k) / 20 < ρ ∧ ρ ≤ Real.sqrt ((2:ℝ)^k) := by
  have ha := lattice_local_sigma_ge h1
  have hb := lattice_local_radius_le hk h2 hhi
  have hS : 0 ≤ Real.sqrt ((2:ℝ)^k) := Real.sqrt_nonneg _
  constructor <;> linarith

theorem lattice_small_const_origin (α : ℝ) : 1 / (1/33 : ℝ)^(α/2) = (33:ℝ)^(α/2) := by
  rw [one_div, one_div, Real.inv_rpow (by norm_num), inv_inv]

/-- The constant of the near case: `2^(alpha/2) / 4^(-alpha/2) = 8^(alpha/2)`. -/
theorem lattice_small_const_near (α : ℝ) (P : ℝ≥0∞) :
    ENNReal.ofReal ((2:ℝ)^(α/2)) * P / ENNReal.ofReal ((1/4 : ℝ)^(α/2)) =
      ENNReal.ofReal ((8:ℝ)^(α/2)) * P := by
  have h : (2:ℝ)^(α/2) / (1/4 : ℝ)^(α/2) = (8:ℝ)^(α/2) := by
    rw [← Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
  rw [← h, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.mul_div_right_comm]

/-- The constant of the mass case with `M = 20`:
`8 / c(20) = 12288 * 8640001^(alpha/2)`. -/
theorem lattice_small_const_mass (α : ℝ) :
    8 / ((1 / (21600 * (20:ℝ)^2 + 1))^(α/2) / 1536) = 12288 * (8640001:ℝ)^(α/2) := by
  have hN : (21600 * (20:ℝ)^2 + 1) = 8640001 := by norm_num
  have hpos : 0 < (8640001:ℝ)^(α/2) := by positivity
  rw [hN, one_div, Real.inv_rpow (by norm_num)]
  field_simp
  norm_num

/-- If `w y <= K w z` for all `y` in `S` and `z` in `T`, one number `m > 0`
separates them: `m <= w` on `T` and `w <= K m` on `S`. This is
"`max_S w <= K min_T w`" without attaining the extrema. -/
theorem lattice_small_inf_pivot {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 < w x) {S T : Set X}
    {K : ℝ} (hK : 0 < K) {y0 : X} (hy0 : y0 ∈ S) {z0 : X} (hz0 : z0 ∈ T)
    (h : ∀ y ∈ S, ∀ z ∈ T, w y ≤ K * w z) :
    ∃ m : ℝ, 0 < m ∧ (∀ z ∈ T, m ≤ w z) ∧ ∀ y ∈ S, w y ≤ K * m := by
  have hbdd : BddBelow (w '' T) := ⟨0, by
    rintro _ ⟨z, _, rfl⟩
    exact (hw z).le⟩
  have hne : (w '' T).Nonempty := ⟨w z0, z0, hz0, rfl⟩
  have hkey : ∀ y ∈ S, w y / K ≤ sInf (w '' T) := by
    intro y hy
    apply le_csInf hne
    rintro _ ⟨z, hz, rfl⟩
    rw [div_le_iff₀ hK]
    linarith [h y hy z hz]
  refine ⟨sInf (w '' T), lt_of_lt_of_le (div_pos (hw y0) hK) (hkey y0 hy0),
    fun z hz => csInf_le hbdd ⟨z, hz, rfl⟩, fun y hy => ?_⟩
  have h' := hkey y hy
  rw [div_le_iff₀ hK] at h'
  linarith

/-! ### Centre near the origin -/

/-- Paper: for a ball of radius at most 8 centred in `{|x| < 16}`, the doubled
ball lies in `{|x| <= 32}`, so `33^(-alpha/2) <= w <= 1` on it. -/
theorem lattice_small_origin_bounds {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : ‖x0‖ < 16) {ρ : ℝ} (hρ : ρ ≤ 8) {y : LatticeSpace}
    (hy : y ∈ ball x0 (2 * ρ)) :
    (1/33 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α y ∧
      latticeWeight latticeValleys α y ≤ 1 := by
  rw [mem_ball] at hy
  have h := (lattice_local_norm_dist y x0).1
  exact lattice_local_near_origin hα (by linarith)

/-- Poincare at every ball of radius at most 8 centred in `{|x| < 16}`, from
the Poincare inequality of Lebesgue measure at the same ball. -/
theorem lattice_small_poincare_origin_at {α : ℝ} (hα : 0 ≤ α) {P0 : ℝ≥0∞} {x0 : LatticeSpace}
    (hx0 : ‖x0‖ < 16) {ρ : ℝ} (hρ : ρ ≤ 8)
    (h0 : poincareAt (volume : Measure LatticeSpace) (fun _ => 1) P0 1 x0 ρ) :
    poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((33:ℝ)^(α/2)) * P0) 1 x0 ρ := by
  have hb : ∀ x ∈ ball x0 (1 * ρ), (1/33 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α x ∧
      latticeWeight latticeValleys α x ≤ 1 := by
    intro x hx
    rw [one_mul] at hx
    exact lattice_small_origin_bounds hα hx0 hρ (ball_subset_ball_scaled x0 ρ one_le_two hx)
  have h := poincareAt_of_bounds (by positivity : (0:ℝ) < (1/33 : ℝ)^(α/2)) le_rfl hb h0
  rwa [lattice_small_const_origin] at h

/-- Doubling at every ball of radius at most 8 centred in `{|x| < 16}`. -/
theorem lattice_small_doubling_origin_at {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : ‖x0‖ < 16) {ρ : ℝ} (hρ : ρ ≤ 8) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((33:ℝ)^(α/2)) * 8) x0 ρ := by
  have h := doublingAt_of_bounds_three (w := latticeWeight latticeValleys α)
    (by positivity : (0:ℝ) < (1/33 : ℝ)^(α/2)) (M := 1) (a := x0) (r := ρ)
    (fun x hx => (lattice_small_origin_bounds hα hx0 hρ hx).2)
    (fun x hx => (lattice_small_origin_bounds hα hx0 hρ
      (ball_subset_ball_scaled x0 ρ one_le_two hx)).1)
  rwa [lattice_small_const_origin] at h

/-! ### Far case -/

/-- Far case, Poincare: constant `9^(alpha/2)` times the Lebesgue constant.
No restriction on the radius or on the centre. -/
theorem lattice_small_poincare_far_at {α : ℝ} (hα : 0 ≤ α) {P0 : ℝ≥0∞} {x0 : LatticeSpace}
    {ρ : ℝ} (hρ0 : 0 < ρ) (hfar : 2 * ρ ≤ infDist x0 latticeValleys)
    (h0 : poincareAt (volume : Measure LatticeSpace) (fun _ => 1) P0 1 x0 ρ) :
    poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((9:ℝ)^(α/2)) * P0) 1 x0 ρ := by
  obtain ⟨m, hm, hlo, hhi⟩ := lattice_small_inf_pivot
    (w := latticeWeight latticeValleys α) (latticeWeight_pos _ _)
    (S := ball x0 ρ) (T := ball x0 ρ) (by positivity : (0:ℝ) < (9:ℝ)^(α/2))
    (mem_ball_self hρ0) (mem_ball_self hρ0)
    (fun y hy z hz => lattice_local_far_variation latticeValleys hα hfar hy hz)
  have hb : ∀ x ∈ ball x0 (1 * ρ), m ≤ latticeWeight latticeValleys α x ∧
      latticeWeight latticeValleys α x ≤ (9:ℝ)^(α/2) * m := by
    intro x hx
    rw [one_mul] at hx
    exact ⟨hlo x hx, hhi x hx⟩
  have h := poincareAt_of_bounds hm le_rfl hb h0
  rwa [mul_div_cancel_right₀ _ hm.ne'] at h

/-- Far case, doubling: constant `8 * 16^(alpha/2)`. -/
theorem lattice_small_doubling_far_at {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hfar : 2 * ρ ≤ infDist x0 latticeValleys) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((16:ℝ)^(α/2)) * 8) x0 ρ := by
  obtain ⟨m, hm, hlo, hhi⟩ := lattice_small_inf_pivot
    (w := latticeWeight latticeValleys α) (latticeWeight_pos _ _)
    (S := ball x0 (2 * ρ)) (T := ball x0 ρ) (by positivity : (0:ℝ) < (16:ℝ)^(α/2))
    (mem_ball_self (by linarith)) (mem_ball_self hρ0)
    (fun y hy z hz => lattice_local_far_sup_le_inf latticeValleys hα hfar hy hz)
  have h := doublingAt_of_bounds_three hm hhi hlo
  rwa [mul_div_cancel_right₀ _ hm.ne'] at h

/-! ### Near case -/

/-- Near case, Poincare. The hypothesis is the Poincare inequality of the
circle weights at the ball `B(x_0, rho)` itself; the comparison
`(eq:wcompare)` is used on that ball only. Constant `8^(alpha/2)` times the
constant of the circle weights. -/
theorem lattice_small_poincare_near_at {α : ℝ} (hα : 0 ≤ α) {Pc : ℝ≥0∞} {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10)
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ)
    (hc : ∀ k : ℕ, 4 ≤ k → ∀ (i : Fin (latticeLayerCount k))
      (j : Fin (latticeCirclesPerLayer k)),
      poincareAt (volume : Measure LatticeSpace)
        (circleWeight (indexedLatticeCircle k i j) α) Pc 1 x0 ρ) :
    poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((8:ℝ)^(α/2)) * Pc) 1 x0 ρ := by
  obtain ⟨k', i, j, -, hcmp⟩ := lattice_local_near_comparison_exists hα hx0 hρ hnear
  have hs : 0 < (1 + ‖x0‖)^(-(α/2)) := Real.rpow_pos_of_pos (by positivity) _
  have h1 := poincareAt_const_mul hs (hc k'.val k'.property i j)
  have hcmp' : ∀ x ∈ ball x0 (1 * ρ),
      (1/4 : ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
          circleWeight (indexedLatticeCircle k'.val i j) α x) ≤
        latticeWeight latticeValleys α x ∧
      latticeWeight latticeValleys α x ≤
        (2:ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
          circleWeight (indexedLatticeCircle k'.val i j) α x) := by
    intro x hx
    rw [one_mul] at hx
    exact hcmp x hx
  have h2 := poincareAt_transfer_local_real (by positivity : (0:ℝ) < (1/4 : ℝ)^(α/2))
    (by positivity : (0:ℝ) ≤ (2:ℝ)^(α/2)) le_rfl hcmp' h1
  rwa [lattice_small_const_near] at h2

/-- Near case, doubling, `rho <= sigma_0 / 20`. The hypothesis is doubling of
the circle weights at the ball `B(x_0, rho)` itself, that is
`mu_C(2B) <= D mu_C(B)`; the comparison `(eq:wcompare)` is used on `2B`. -/
theorem lattice_small_doubling_near_at {α : ℝ} (hα : 0 ≤ α) {Dc : ℝ≥0∞} {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 20)
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ)
    (hc : ∀ k : ℕ, 4 ≤ k → ∀ (i : Fin (latticeLayerCount k))
      (j : Fin (latticeCirclesPerLayer k)),
      doublingAt (volume : Measure LatticeSpace)
        (circleWeight (indexedLatticeCircle k i j) α) Dc x0 ρ) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal ((8:ℝ)^(α/2)) * Dc) x0 ρ := by
  obtain ⟨k', i, j, -, hcmp⟩ := lattice_local_near_comparison_double hα hx0 hρ hnear
  have hs : 0 < (1 + ‖x0‖)^(-(α/2)) := Real.rpow_pos_of_pos (by positivity) _
  have h1 := doublingAt_const_mul hs (hc k'.val k'.property i j)
  have hcmp' : ∀ x ∈ ball x0 (2 * ρ),
      (1/4 : ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
          circleWeight (indexedLatticeCircle k'.val i j) α x) ≤
        latticeWeight latticeValleys α x ∧
      latticeWeight latticeValleys α x ≤
        (2:ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
          circleWeight (indexedLatticeCircle k'.val i j) α x) :=
    fun x hx => hcmp x hx
  have h2 := doublingAt_transfer_local_real (by positivity : (0:ℝ) < (1/4 : ℝ)^(α/2))
    (by positivity : (0:ℝ) ≤ (2:ℝ)^(α/2)) hcmp' h1
  rwa [lattice_small_const_near] at h2

/-- Doubling for `rho >= sigma_0 / 20`, from the mass bound:
`mu(2B) <= |2B| = 8 |B| <= (8 / c) mu(B)`. No circle weight enters, and
there is no upper bound on the radius. -/
theorem lattice_small_doubling_mass_at {α : ℝ} (hα : 0 ≤ α) (x0 : LatticeSpace) {ρ : ℝ}
    (hρ : Real.sqrt (1 + ‖x0‖) / 20 ≤ ρ) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal (12288 * (8640001:ℝ)^(α/2))) x0 ρ := by
  have h := lattice_mass_double_ball hα (by norm_num : (1:ℝ) ≤ 20) x0 hρ
  rw [lattice_small_const_mass] at h
  exact h

/-! ### One small ball, all cases -/

/-- **Poincare at one small ball.** From the Poincare inequality of Lebesgue
measure and of the lattice circle weights at the same ball, with constants
`P0` and `Pc`: the lattice weight satisfies it there with constant
`max (33^(alpha/2) P0) (8^(alpha/2) Pc)`. -/
theorem lattice_small_ball_poincare_at {α : ℝ} (hα : 0 ≤ α) {P0 Pc : ℝ≥0∞}
    {x0 : LatticeSpace} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10)
    (h0 : poincareAt (volume : Measure LatticeSpace) (fun _ => 1) P0 1 x0 ρ)
    (hc : ∀ k : ℕ, 4 ≤ k → ∀ (i : Fin (latticeLayerCount k))
      (j : Fin (latticeCirclesPerLayer k)),
      poincareAt (volume : Measure LatticeSpace)
        (circleWeight (indexedLatticeCircle k i j) α) Pc 1 x0 ρ) :
    poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (max (ENNReal.ofReal ((33:ℝ)^(α/2)) * P0) (ENNReal.ofReal ((8:ℝ)^(α/2)) * Pc))
      1 x0 ρ := by
  rcases lt_or_ge ‖x0‖ 16 with hx0 | hx0
  · exact poincareAt_mono (le_max_left _ _) (lattice_small_poincare_origin_at hα hx0
      (by linarith [lattice_small_radius_le_half hx0 hρ]) h0)
  · rcases le_or_gt (2 * ρ) (infDist x0 latticeValleys) with hfar | hnear
    · refine poincareAt_mono (le_trans ?_ (le_max_left _ _))
        (lattice_small_poincare_far_at hα hρ0 hfar h0)
      exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity))) _
    · exact poincareAt_mono (le_max_right _ _)
        (lattice_small_poincare_near_at hα hx0 hρ hnear.le hc)

/-- **Doubling at one small ball.** From doubling of the lattice circle
weights at the same ball, with constant `Dc`: the lattice weight is doubling
there with constant
`max (8 * 33^(alpha/2)) (max (8^(alpha/2) Dc) (12288 * 8640001^(alpha/2)))`. -/
theorem lattice_small_ball_doubling_at {α : ℝ} (hα : 0 ≤ α) {Dc : ℝ≥0∞}
    {x0 : LatticeSpace} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10)
    (hc : ∀ k : ℕ, 4 ≤ k → ∀ (i : Fin (latticeLayerCount k))
      (j : Fin (latticeCirclesPerLayer k)),
      doublingAt (volume : Measure LatticeSpace)
        (circleWeight (indexedLatticeCircle k i j) α) Dc x0 ρ) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (max (ENNReal.ofReal ((33:ℝ)^(α/2)) * 8)
        (max (ENNReal.ofReal ((8:ℝ)^(α/2)) * Dc)
          (ENNReal.ofReal (12288 * (8640001:ℝ)^(α/2))))) x0 ρ := by
  rcases lt_or_ge ‖x0‖ 16 with hx0 | hx0
  · exact doublingAt_mono (le_max_left _ _) (lattice_small_doubling_origin_at hα hx0
      (by linarith [lattice_small_radius_le_half hx0 hρ]))
  · rcases le_or_gt (2 * ρ) (infDist x0 latticeValleys) with hfar | hnear
    · refine doublingAt_mono (le_trans ?_ (le_max_left _ _))
        (lattice_small_doubling_far_at hα hρ0 hfar)
      exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity))) _
    · rcases le_or_gt ρ (Real.sqrt (1 + ‖x0‖) / 20) with hsmall | hbig
      · exact doublingAt_mono ((le_max_left _ _).trans (le_max_right _ _))
          (lattice_small_doubling_near_at hα hx0 hsmall hnear.le hc)
      · exact doublingAt_mono ((le_max_right _ _).trans (le_max_right _ _))
          (lattice_small_doubling_mass_at hα x0 hbig.le)

/-! ### The two statements of the session -/

/-- **Small balls, Poincare.** Modulo the Poincare inequality of Lebesgue
measure and `lem:circle`: the lattice weight satisfies the strong Poincare
inequality at every ball of radius at most `sigma(x_0) / 10`, with one
constant. -/
theorem lattice_small_ball_poincare {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hleb : LebesguePoincarePremise) (hcircle : CircleLemmaPremise alpha) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
      rho ≤ Real.sqrt (1 + ‖x0‖) / 10 →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 x0 rho := by
  obtain ⟨P0, hP0, h0⟩ := hleb
  obtain ⟨Dc, Pc, -, hPc, hc⟩ := hcircle
  refine ⟨max (ENNReal.ofReal ((33:ℝ)^(alpha/2)) * P0) (ENNReal.ofReal ((8:ℝ)^(alpha/2)) * Pc),
    ?_, fun x0 rho h1 h2 => lattice_small_ball_poincare_at halpha h1 h2 (h0 x0 rho h1)
      (fun k hk i j => (hc k hk i j).2 x0 rho h1)⟩
  exact (max_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP0.lt_top)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPc.lt_top)).ne

/-- **Small balls, doubling.** Modulo `lem:circle`: the lattice weight is
doubling at every ball of radius at most `sigma(x_0) / 10`, with one
constant. -/
theorem lattice_small_ball_doubling {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcircle : CircleLemmaPremise alpha) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
      rho ≤ Real.sqrt (1 + ‖x0‖) / 10 →
      doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        D x0 rho := by
  obtain ⟨Dc, Pc, hDc, -, hc⟩ := hcircle
  refine ⟨max (ENNReal.ofReal ((33:ℝ)^(alpha/2)) * 8)
      (max (ENNReal.ofReal ((8:ℝ)^(alpha/2)) * Dc)
        (ENNReal.ofReal (12288 * (8640001:ℝ)^(alpha/2)))),
    ?_, fun x0 rho h1 h2 => lattice_small_ball_doubling_at halpha h1 h2
      (fun k hk i j => (hc k hk i j).1 x0 rho h1)⟩
  exact (max_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num))
    (max_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDc.lt_top) ENNReal.ofReal_lt_top)).ne

end BrownRadial
