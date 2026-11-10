import LatticeGeometry
import Polar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Volume growth of the lattice weight of `thm:B` (part (c)), by a covering
argument that uses only Euclidean ball volumes: the tubes around the latitude
circles are covered by finitely many balls centred on the circles.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### Elementary facts on the weight -/

theorem latticeWeight_le_one {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {α : ℝ}
    (hα : 0 ≤ α) (x : E) : latticeWeight Γ α x ≤ 1 := by
  unfold latticeWeight
  apply Real.rpow_le_one (by positivity) _ (by positivity)
  rw [div_le_one (by positivity)]
  linarith [norm_nonneg x]

theorem latticeWeight_continuous {E : Type*} [NormedAddCommGroup E] (Γ : Set E) (α : ℝ) :
    Continuous (latticeWeight Γ α) := by
  unfold latticeWeight
  have hd : Continuous (fun x : E => infDist x Γ) := continuous_infDist_pt Γ
  apply Continuous.rpow_const
  · exact ((continuous_const.add (hd.pow 2)).div
      ((continuous_const.add continuous_norm).add (hd.pow 2)) (fun x => by positivity))
  · intro x
    left
    positivity

/-- Lower bound for the weight from a lower bound on its base. -/
theorem latticeWeight_lower {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {α : ℝ}
    (hα : 0 ≤ α) {x : E} {q : ℝ} (hq : 0 < q)
    (h : q * (1 + ‖x‖ + (infDist x Γ)^2) ≤ 1 + (infDist x Γ)^2) :
    q ^ (α/2) ≤ latticeWeight Γ α x := by
  unfold latticeWeight
  apply Real.rpow_le_rpow hq.le _ (by positivity)
  rw [le_div_iff₀ (by positivity)]
  exact h

theorem lattice_ball_volume_real (x : LatticeSpace) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = 4/3 * Real.pi * r^3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem lattice_volume_upper {α : ℝ} (hα : 0 ≤ α) {r : ℝ} (hr : 0 ≤ r) :
    weightedBallVolume volume (latticeWeight latticeValleys α) r ≤ (4/3) * Real.pi * r^3 := by
  unfold weightedBallVolume
  have hw := latticeWeight_continuous latticeValleys α
  have hi : IntegrableOn (latticeWeight latticeValleys α) (ball (0 : LatticeSpace) r) volume :=
    (hw.continuousOn.integrableOn_compact (isCompact_closedBall (0 : LatticeSpace) r)).mono_set
      ball_subset_closedBall
  have h := setIntegral_mono_on hi (integrableOn_const (C := (1:ℝ)) measure_ball_lt_top.ne)
    measurableSet_ball (fun x _ => latticeWeight_le_one latticeValleys hα x)
  rw [setIntegral_const, smul_eq_mul, mul_one, lattice_ball_volume_real _ hr] at h
  exact h

/-! ### Covering a latitude circle by balls -/

theorem latitudePoint_apply_zero (R θ φ : ℝ) :
    latitudePoint R θ φ 0 = R*Real.sin θ*Real.cos φ := by simp [latitudePoint]

theorem latitudePoint_apply_one (R θ φ : ℝ) :
    latitudePoint R θ φ 1 = R*Real.sin θ*Real.sin φ := by simp [latitudePoint]

theorem latitudePoint_apply_two (R θ φ : ℝ) :
    latitudePoint R θ φ 2 = R*Real.cos θ := by simp [latitudePoint]

/-- Two points of one latitude circle are no farther apart than the radius
times their azimuth difference. -/
theorem latitudePoint_dist_le (R θ φ ψ : ℝ) :
    dist (latitudePoint R θ φ) (latitudePoint R θ ψ) ≤ |R| * |φ - ψ| := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three, latitudePoint_apply_zero, latitudePoint_apply_one,
    latitudePoint_apply_two, Real.dist_eq, sq_abs]
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ - ψ)
  rw [Real.cos_sub] at hc
  have h1 := Real.sin_sq_add_cos_sq φ
  have h2 := Real.sin_sq_add_cos_sq ψ
  have h3 := Real.sin_sq_add_cos_sq θ
  have key : (R*Real.sin θ*Real.cos φ - R*Real.sin θ*Real.cos ψ)^2 +
      (R*Real.sin θ*Real.sin φ - R*Real.sin θ*Real.sin ψ)^2 + (R*Real.cos θ - R*Real.cos θ)^2 =
      R^2 * Real.sin θ^2 * (2 - 2*(Real.cos φ*Real.cos ψ + Real.sin φ*Real.sin ψ)) := by
    linear_combination (R^2 * Real.sin θ^2) * h1 + (R^2 * Real.sin θ^2) * h2
  rw [key, mul_pow, sq_abs, sq_abs]
  have hs1 : Real.sin θ^2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos θ)]
  have hb : 2 - 2*(Real.cos φ*Real.cos ψ + Real.sin φ*Real.sin ψ) ≤ (φ-ψ)^2 := by linarith
  have hb0 : 0 ≤ 2 - 2*(Real.cos φ*Real.cos ψ + Real.sin φ*Real.sin ψ) := by
    have := Real.cos_le_one (φ - ψ)
    rw [Real.cos_sub] at this
    linarith
  calc R^2 * Real.sin θ^2 * (2 - 2*(Real.cos φ*Real.cos ψ + Real.sin φ*Real.sin ψ))
      ≤ R^2 * 1 * (φ-ψ)^2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs1 (sq_nonneg R)) hb hb0
        positivity
    _ = R^2 * (φ-ψ)^2 := by ring

/-- Every point of a latitude circle has an azimuth in `[-π, π]`. -/
theorem latitudeCircle_param {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ' : θ < Real.pi)
    {y : LatticeSpace} (hy : y ∈ latitudeCircle R θ) :
    ∃ φ : ℝ, -Real.pi ≤ φ ∧ φ ≤ Real.pi ∧ y = latitudePoint R θ φ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθ'
  have hspos : 0 < R * Real.sin θ := mul_pos hR hs
  have hnorm : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = R^2 := by
    have h := EuclideanSpace.norm_sq_eq y
    rw [hy.1, Fin.sum_univ_three] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h.symm
  have h01 : y 0 ^ 2 + y 1 ^ 2 = (R * Real.sin θ)^2 := by
    rw [hy.2] at hnorm
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, y 0 = R * Real.sin θ * c := ⟨y 0 / (R * Real.sin θ), by field_simp⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, y 1 = R * Real.sin θ * t := ⟨y 1 / (R * Real.sin θ), by field_simp⟩
  have hct : c^2 + t^2 = 1 := by
    rw [hc, ht] at h01
    have hne : (R * Real.sin θ)^2 ≠ 0 := by positivity
    have : (R * Real.sin θ)^2 * (c^2 + t^2) = (R * Real.sin θ)^2 * 1 := by nlinarith
    exact mul_left_cancel₀ hne this
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [sq_nonneg t]
  have hsq : Real.sqrt (1 - c^2) = |t| := by
    rw [show 1 - c^2 = t^2 by linarith, Real.sqrt_sq_eq_abs]
  have hpi := Real.pi_pos
  by_cases ht0 : 0 ≤ t
  · refine ⟨Real.arccos c, by linarith [Real.arccos_nonneg c], Real.arccos_le_pi c, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change y 0 = latitudePoint R θ (Real.arccos c) 0
      rw [latitudePoint_apply_zero, Real.cos_arccos hc1.1 hc1.2, hc]
    · change y 1 = latitudePoint R θ (Real.arccos c) 1
      rw [latitudePoint_apply_one, Real.sin_arccos, hsq, abs_of_nonneg ht0, ht]
    · change y 2 = latitudePoint R θ (Real.arccos c) 2
      rw [latitudePoint_apply_two, hy.2]
  · have ht0' : t < 0 := not_le.mp ht0
    refine ⟨-Real.arccos c, by linarith [Real.arccos_le_pi c],
      by linarith [Real.arccos_nonneg c], ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change y 0 = latitudePoint R θ (-Real.arccos c) 0
      rw [latitudePoint_apply_zero, Real.cos_neg, Real.cos_arccos hc1.1 hc1.2, hc]
    · change y 1 = latitudePoint R θ (-Real.arccos c) 1
      rw [latitudePoint_apply_one, Real.sin_neg, Real.sin_arccos, hsq, abs_of_neg ht0', ht]
      ring
    · change y 2 = latitudePoint R θ (-Real.arccos c) 2
      rw [latitudePoint_apply_two, hy.2]

/-- Azimuths of the centres of the covering balls. -/
noncomputable def coverAngle (n : ℕ) (l : Fin n) : ℝ :=
  -Real.pi + 2 * Real.pi * ((l.val : ℝ) + 1/2) / n

/-- A latitude circle is covered by `n` closed balls of radius `R π / n`
centred at equally spaced points of the circle. -/
theorem latitudeCircle_cover {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ' : θ < Real.pi)
    {n : ℕ} (hn : 0 < n) {y : LatticeSpace} (hy : y ∈ latitudeCircle R θ) :
    ∃ l : Fin n, dist y (latitudePoint R θ (coverAngle n l)) ≤ R * Real.pi / n := by
  obtain ⟨φ, h1, h2, rfl⟩ := latitudeCircle_param hR hθ hθ' hy
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have ht0 : 0 ≤ (φ + Real.pi) * n / (2*Real.pi) := by
    apply div_nonneg (mul_nonneg (by linarith) hnr.le) (by positivity)
  have ht1 : (φ + Real.pi) * n / (2*Real.pi) ≤ n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨l, hl⟩ := midpoint_grid_cover hn ht0 ht1
  refine ⟨l, (latitudePoint_dist_le R θ φ _).trans ?_⟩
  have he : φ - coverAngle n l =
      (2*Real.pi/n) * ((φ + Real.pi) * n / (2*Real.pi) - ((l.val:ℝ)+1/2)) := by
    unfold coverAngle
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hR, abs_of_pos (by positivity)]
  calc R * (2*Real.pi/n * |(φ + Real.pi) * n / (2*Real.pi) - ((l.val:ℝ)+1/2)|)
      ≤ R * (2*Real.pi/n * (1/2)) := by gcongr
    _ = R * Real.pi / n := by ring

/-! ### Covering the tubes around the lattice circles -/

/-- Centres of the balls covering the circle with index `(k,i,j)`. -/
noncomputable def coverCenter (k n : ℕ) (i : Fin (latticeLayerCount k))
    (j : Fin (latticeCirclesPerLayer k)) (l : Fin n) : LatticeSpace :=
  latitudePoint (latticeCircleRadius k i)
    (latticePolarAngle k (latticeAngleIndex k (i,j))) (coverAngle n l)

theorem indexedLatticeCircle_cover (k : ℕ) (i : Fin (latticeLayerCount k))
    (j : Fin (latticeCirclesPerLayer k)) {n : ℕ} (hn : 0 < n) {y : LatticeSpace}
    (hy : y ∈ indexedLatticeCircle k i j) :
    ∃ l : Fin n, dist y (coverCenter k n i j l) ≤ (2:ℝ)^(k+1) * Real.pi / n := by
  have hb := latticeCircleRadius_bounds k i
  have ha := latticePolarAngle_bounds k (latticeAngleIndex k (i,j))
  obtain ⟨l, hl⟩ := latitudeCircle_cover (lt_of_lt_of_le (by positivity) hb.1) ha.1 ha.2 hn hy
  refine ⟨l, hl.trans ?_⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  gcongr
  exact hb.2.le

/-- A lattice point within `τ` of a point of shell `k` lies in one of the
three shells `k-1`, `k`, `k+1`. -/
theorem lattice_shell_localization {k k' : ℕ} (i : Fin (latticeLayerCount k'))
    (j : Fin (latticeCirclesPerLayer k')) {x y : LatticeSpace} {τ : ℝ} (hk : 1 ≤ k)
    (hx1 : (2:ℝ)^k ≤ ‖x‖) (hx2 : ‖x‖ + τ ≤ (2:ℝ)^(k+2)) (hτ : τ ≤ (2:ℝ)^(k-1))
    (hd : dist x y < τ) (hy : y ∈ indexedLatticeCircle k' i j) :
    k - 1 ≤ k' ∧ k' ≤ k + 1 := by
  have hyn := indexedLatticeCircle_in_shell k' i j hy
  change (2:ℝ)^k' ≤ ‖y‖ ∧ ‖y‖ < (2:ℝ)^(k'+1) at hyn
  have h1 : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  have hpow : (2:ℝ)^k = 2 * 2^(k-1) := by
    rw [← pow_succ']
    congr 1
    omega
  constructor
  · have h : (2:ℝ)^(k-1) < (2:ℝ)^(k'+1) := by linarith [hyn.2]
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega
  · have h : (2:ℝ)^k' < (2:ℝ)^(k+2) := by linarith [hyn.1]
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

/-- Points of shell `k` closer than `ρ` to the valleys. -/
def shellBad (k : ℕ) (ρ : ℝ) : Set LatticeSpace :=
  {x | (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(k+1) ∧ infDist x latticeValleys < ρ}

/-- Points of shell `k` at distance at least `ρ` from the valleys. -/
def shellGood (k : ℕ) (ρ : ℝ) : Set LatticeSpace :=
  {x | (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(k+1) ∧ ρ ≤ infDist x latticeValleys}

theorem shellGood_measurable (k : ℕ) (ρ : ℝ) : MeasurableSet (shellGood k ρ) := by
  have hn : Measurable (fun x : LatticeSpace => ‖x‖) := measurable_norm
  have hd : Measurable (fun x : LatticeSpace => infDist x latticeValleys) :=
    (continuous_infDist_pt _).measurable
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_lt hn measurable_const).inter (measurableSet_le measurable_const hd))

theorem shellBad_subset {k n : ℕ} (hk : 5 ≤ k) (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ≤ (2:ℝ)^(k-1)) (hnρ : (2:ℝ)^(k+2) * Real.pi / n ≤ ρ) :
    shellBad k ρ ⊆ ⋃ m : Fin 3, ⋃ i : Fin (latticeLayerCount (k-1+m.val)),
      ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ⋃ l : Fin n,
        ball (coverCenter (k-1+m.val) n i j l) (2*ρ) := by
  rintro x ⟨hx1, hx2, hx3⟩
  obtain ⟨y, hy, hd⟩ := (infDist_lt_iff latticeValleys_nonempty).mp hx3
  obtain ⟨⟨k', hk'⟩, hy⟩ := mem_iUnion.mp hy
  obtain ⟨i, hy⟩ := mem_iUnion.mp hy
  obtain ⟨j, hy⟩ := mem_iUnion.mp hy
  dsimp only at i j hy
  have hpm : (2:ℝ)^(k-1) ≤ (2:ℝ)^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp2 : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by rw [pow_succ]; ring
  have hloc := lattice_shell_localization i j (by omega) hx1 (by linarith) hρ hd hy
  obtain ⟨m, rfl⟩ : ∃ m : Fin 3, k' = k - 1 + m.val :=
    ⟨⟨k' - (k-1), by omega⟩, by simp only; omega⟩
  obtain ⟨l, hl⟩ := indexedLatticeCircle_cover _ i j hn hy
  simp only [mem_iUnion, mem_ball]
  refine ⟨m, i, j, l, ?_⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hle : (2:ℝ)^(k-1+m.val+1) * Real.pi / n ≤ ρ := by
    refine le_trans ?_ hnρ
    have hpi := Real.pi_pos
    have : (2:ℝ)^(k-1+m.val+1) ≤ (2:ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  calc dist x (coverCenter (k-1+m.val) n i j l)
      ≤ dist x y + dist y (coverCenter (k-1+m.val) n i j l) := dist_triangle _ _ _
    _ < ρ + ρ := add_lt_add_of_lt_of_le hd (hl.trans hle)
    _ = 2*ρ := by ring

theorem shellBad_volume_le {k n : ℕ} (hk : 5 ≤ k) (hn : 0 < n) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ (2:ℝ)^(k-1)) (hnρ : (2:ℝ)^(k+2) * Real.pi / n ≤ ρ) :
    volume.real (shellBad k ρ) ≤ 3 * (2:ℝ)^(k+3) * n * (4/3 * Real.pi * (2*ρ)^3) := by
  have hsub := shellBad_subset hk hn hρ hnρ
  have hfin : volume (⋃ m : Fin 3, ⋃ i : Fin (latticeLayerCount (k-1+m.val)),
      ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ⋃ l : Fin n,
        ball (coverCenter (k-1+m.val) n i j l) (2*ρ)) ≠ ∞ := by
    apply (Bornology.IsBounded.measure_lt_top _).ne
    simp only [Bornology.isBounded_iUnion, isBounded_ball, implies_true]
  refine (measureReal_mono hsub hfin).trans ?_
  have h2ρ : 0 ≤ 2*ρ := by positivity
  calc volume.real (⋃ m : Fin 3, ⋃ i : Fin (latticeLayerCount (k-1+m.val)),
        ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ⋃ l : Fin n,
          ball (coverCenter (k-1+m.val) n i j l) (2*ρ))
      ≤ ∑ m : Fin 3, ∑ i : Fin (latticeLayerCount (k-1+m.val)),
        ∑ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ∑ l : Fin n,
          volume.real (ball (coverCenter (k-1+m.val) n i j l) (2*ρ)) := by
        refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun m _ => ?_)
        refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact measureReal_iUnion_fintype_le _
    _ = ∑ m : Fin 3, (latticeCircleCount (k-1+m.val) : ℝ) * n *
          (4/3 * Real.pi * (2*ρ)^3) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [lattice_ball_volume_real _ h2ρ, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [← lattice_counts_product]
        push_cast
        ring
    _ ≤ ∑ _m : Fin 3, (2:ℝ)^(k+3) * n * (4/3 * Real.pi * (2*ρ)^3) := by
        apply Finset.sum_le_sum
        intro m _
        have hpi := Real.pi_pos
        have hN : (latticeCircleCount (k-1+m.val) : ℝ) ≤ (2:ℝ)^(k+3) := by
          unfold latticeCircleCount
          push_cast
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        gcongr
    _ = 3 * (2:ℝ)^(k+3) * n * (4/3 * Real.pi * (2*ρ)^3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem lattice_half_powers (k : ℕ) :
    (2:ℝ)^(k/2) * (2:ℝ)^((k+1)/2) = (2:ℝ)^k ∧ (2:ℝ)^(k/2) ≤ (2:ℝ)^((k+1)/2) ∧
      (2:ℝ)^((k+1)/2) ≤ 2 * (2:ℝ)^(k/2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← pow_add]
    congr 1
    omega
  · exact pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- At least 4/7 of the volume of shell `k` stays `2^(k/2)/32` away from the valleys. -/
theorem shellGood_volume_ge {k : ℕ} (hk : 5 ≤ k) :
    16/3 * Real.pi * ((2:ℝ)^k)^3 ≤ volume.real (shellGood k ((2:ℝ)^(k/2)/32)) := by
  obtain ⟨hab, hale, hb2⟩ := lattice_half_powers k
  have hpi := Real.pi_pos
  have hapos : 0 < (2:ℝ)^(k/2) := by positivity
  have hb1 : (1:ℝ) ≤ (2:ℝ)^((k+1)/2) := one_le_pow₀ (by norm_num)
  have hTpos : 0 < (2:ℝ)^k := by positivity
  have hpow1 : (2:ℝ)^(k+1) = 2*(2:ℝ)^k := by rw [pow_succ]; ring
  have hpow2 : (2:ℝ)^(k+2) = 4*(2:ℝ)^k := by rw [pow_add]; ring
  have hpow3 : (2:ℝ)^(k+3) = 8*(2:ℝ)^k := by rw [pow_add]; ring
  have hpowm : (2:ℝ)^(k-1) = (2:ℝ)^k/2 := by
    have : (2:ℝ)^k = 2 * 2^(k-1) := by
      rw [← pow_succ']
      congr 1
      omega
    linarith
  have hn : 0 < 2^(9+(k+1)/2) := by positivity
  have hncast : ((2^(9+(k+1)/2) : ℕ) : ℝ) = 512 * (2:ℝ)^((k+1)/2) := by
    push_cast
    rw [pow_add]
    norm_num
  have haT : (2:ℝ)^(k/2) ≤ (2:ℝ)^k := by nlinarith
  have hbad := shellBad_volume_le hk hn (ρ := (2:ℝ)^(k/2)/32) (by positivity)
    (by rw [hpowm]; linarith)
    (by
      rw [hncast, div_le_iff₀ (by positivity), hpow2]
      nlinarith [Real.pi_le_four])
  have hbad' : volume.real (shellBad k ((2:ℝ)^(k/2)/32)) ≤ 4 * Real.pi * ((2:ℝ)^k)^3 := by
    refine hbad.trans ?_
    rw [hncast, hpow3]
    have e : 3 * (8*(2:ℝ)^k) * (512 * (2:ℝ)^((k+1)/2)) *
        (4/3 * Real.pi * (2*((2:ℝ)^(k/2)/32))^3) =
        4 * Real.pi * (2:ℝ)^k * ((2:ℝ)^(k/2) * (2:ℝ)^((k+1)/2)) * ((2:ℝ)^(k/2))^2 := by ring
    rw [e, hab]
    have ha2 : ((2:ℝ)^(k/2))^2 ≤ (2:ℝ)^k := by nlinarith
    calc 4 * Real.pi * (2:ℝ)^k * (2:ℝ)^k * ((2:ℝ)^(k/2))^2
        ≤ 4 * Real.pi * (2:ℝ)^k * (2:ℝ)^k * (2:ℝ)^k := by gcongr
      _ = 4 * Real.pi * ((2:ℝ)^k)^3 := by ring
  have hsup : ball (0:LatticeSpace) ((2:ℝ)^k) ∪
      (shellBad k ((2:ℝ)^(k/2)/32) ∪ shellGood k ((2:ℝ)^(k/2)/32)) ⊆
      ball (0:LatticeSpace) ((2:ℝ)^(k+1)) := by
    rintro x (h | ⟨_, h, _⟩ | ⟨_, h, _⟩)
    · rw [mem_ball_zero_iff] at h ⊢
      linarith
    · rwa [mem_ball_zero_iff]
    · rwa [mem_ball_zero_iff]
  have hcov : ball (0:LatticeSpace) ((2:ℝ)^(k+1)) ⊆ ball (0:LatticeSpace) ((2:ℝ)^k) ∪
      (shellBad k ((2:ℝ)^(k/2)/32) ∪ shellGood k ((2:ℝ)^(k/2)/32)) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases h1 : ‖x‖ < (2:ℝ)^k
    · left
      rwa [mem_ball_zero_iff]
    · right
      by_cases h2 : infDist x latticeValleys < (2:ℝ)^(k/2)/32
      · left
        exact ⟨not_lt.mp h1, hx, h2⟩
      · right
        exact ⟨not_lt.mp h1, hx, not_lt.mp h2⟩
  have hbig := (measureReal_mono hcov
    (measure_ne_top_of_subset hsup (measure_ball_lt_top (μ := (volume : Measure LatticeSpace))
      (x := 0) (r := (2:ℝ)^(k+1))).ne)).trans
      ((measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _))
  rw [lattice_ball_volume_real _ (by positivity), lattice_ball_volume_real _ hTpos.le,
    hpow1] at hbig
  have e2 : 4/3 * Real.pi * (2*(2:ℝ)^k)^3 = 32/3 * Real.pi * ((2:ℝ)^k)^3 := by ring
  rw [e2] at hbig
  linarith

/-- On the good part of a shell the weight is bounded below by a constant. -/
theorem latticeWeight_shellGood_lower {α : ℝ} (hα : 0 ≤ α) {k : ℕ} {x : LatticeSpace}
    (hx : x ∈ shellGood k ((2:ℝ)^(k/2)/32)) :
    (1/6145 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α x := by
  obtain ⟨hab, hale, hb2⟩ := lattice_half_powers k
  obtain ⟨hx1, hx2, hx3⟩ := hx
  apply latticeWeight_lower _ hα (by norm_num)
  have hapos : 0 < (2:ℝ)^(k/2) := by positivity
  have hdsq : ((2:ℝ)^(k/2)/32)^2 ≤ (infDist x latticeValleys)^2 :=
    pow_le_pow_left₀ (by positivity) hx3 2
  have he : ((2:ℝ)^(k/2)/32)^2 = ((2:ℝ)^(k/2))^2/1024 := by ring
  rw [he] at hdsq
  have hT : (2:ℝ)^k ≤ 2 * ((2:ℝ)^(k/2))^2 := by nlinarith
  rw [pow_succ] at hx2
  linarith

/-- The mass of a single shell already gives the cubic lower bound. -/
theorem lattice_volume_lower_shell {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 5 ≤ k) {r : ℝ}
    (hr : (2:ℝ)^(k+1) ≤ r) :
    (1/6145 : ℝ)^(α/2) * (16/3 * Real.pi * ((2:ℝ)^k)^3) ≤
      weightedBallVolume volume (latticeWeight latticeValleys α) r := by
  unfold weightedBallVolume
  have hw := latticeWeight_continuous latticeValleys α
  have hGsub : shellGood k ((2:ℝ)^(k/2)/32) ⊆ ball (0:LatticeSpace) r := fun x hx => by
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hx.2.1 hr
  have hi : IntegrableOn (latticeWeight latticeValleys α) (ball (0 : LatticeSpace) r) volume :=
    (hw.continuousOn.integrableOn_compact (isCompact_closedBall (0 : LatticeSpace) r)).mono_set
      ball_subset_closedBall
  have hGfin : volume (shellGood k ((2:ℝ)^(k/2)/32)) ≠ ∞ :=
    measure_ne_top_of_subset hGsub measure_ball_lt_top.ne
  have hc : 0 ≤ (1/6145 : ℝ)^(α/2) := by positivity
  calc (1/6145 : ℝ)^(α/2) * (16/3 * Real.pi * ((2:ℝ)^k)^3)
      ≤ (1/6145 : ℝ)^(α/2) * volume.real (shellGood k ((2:ℝ)^(k/2)/32)) :=
        mul_le_mul_of_nonneg_left (shellGood_volume_ge hk) hc
    _ = ∫ _x in shellGood k ((2:ℝ)^(k/2)/32), (1/6145 : ℝ)^(α/2) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in shellGood k ((2:ℝ)^(k/2)/32), latticeWeight latticeValleys α x :=
        setIntegral_mono_on (integrableOn_const hGfin) (hi.mono_set hGsub)
          (shellGood_measurable _ _) (fun x hx => latticeWeight_shellGood_lower hα hx)
    _ ≤ ∫ x in ball (0:LatticeSpace) r, latticeWeight latticeValleys α x :=
        setIntegral_mono_set hi (ae_of_all _ (fun x => (latticeWeight_pos _ _ x).le))
          hGsub.eventuallyLE

/-- Volume growth of `thm:B`(c), lower half: `V(r) ≥ c r^3` for `r ≥ 64`. -/
theorem lattice_volume_lower {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 64 ≤ r →
      c * r^3 ≤ weightedBallVolume volume (latticeWeight latticeValleys α) r := by
  have hpi := Real.pi_pos
  refine ⟨(1/6145 : ℝ)^(α/2) * (Real.pi/12), by positivity, ?_⟩
  intro r hr
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1:ℝ) ≤ r)
    (by norm_num : (1:ℝ) < 2)
  have hn6 : 6 ≤ n := by
    by_contra h
    have h5 : n + 1 ≤ 6 := by omega
    have h64 : (2:ℝ)^(n+1) ≤ (2:ℝ)^6 := pow_le_pow_right₀ (by norm_num) h5
    have e64 : (2:ℝ)^6 = 64 := by norm_num
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine le_trans ?_ (lattice_volume_lower_shell hα (by omega : 5 ≤ k) hn1)
  have hT : r ≤ 4 * (2:ℝ)^k := by
    rw [pow_succ, pow_succ] at hn2
    linarith
  have hr3 : r^3 ≤ (4 * (2:ℝ)^k)^3 := pow_le_pow_left₀ (by linarith) hT 3
  have hc : 0 ≤ (1/6145 : ℝ)^(α/2) := by positivity
  calc (1/6145 : ℝ)^(α/2) * (Real.pi/12) * r^3
      ≤ (1/6145 : ℝ)^(α/2) * (Real.pi/12) * (4 * (2:ℝ)^k)^3 := by gcongr
    _ = (1/6145 : ℝ)^(α/2) * (16/3 * Real.pi * ((2:ℝ)^k)^3) := by ring

/-- The ball-volume integral converges: the volume test of Theorem A(iii)
does not fire for the lattice weight. -/
theorem lattice_volume_integral_converges {α : ℝ} (hα : 0 ≤ α) :
    IntegrableOn (fun r => r / weightedBallVolume volume (latticeWeight latticeValleys α) r)
      (Ici 1) := by
  have hw : Continuous (latticeWeight latticeValleys α) := latticeWeight_continuous _ _
  have hp : ∀ x, 0 < latticeWeight latticeValleys α x := latticeWeight_pos _ _
  obtain ⟨c, hc, hlow⟩ := lattice_volume_lower hα
  have hAc := sphericalArea_continuous volume hw
  have hVc : Continuous (cumulativeArea (sphericalArea volume (latticeWeight latticeValleys α))) :=
    intervalIntegral.continuous_primitive (fun _ _ => hAc.intervalIntegrable _ _) 0
  have hVpos : ∀ r, 0 < r →
      0 < cumulativeArea (sphericalArea volume (latticeWeight latticeValleys α)) r := fun r hr =>
    intervalIntegral.intervalIntegral_pos_of_pos_on (hAc.intervalIntegrable _ _)
      (fun x hx => sphericalArea_pos volume hw hp hx.1) hr
  have hcont : ContinuousOn
      (fun r => r / weightedBallVolume volume (latticeWeight latticeValleys α) r) (Ici 1) := by
    have h : ContinuousOn (fun r => r /
        cumulativeArea (sphericalArea volume (latticeWeight latticeValleys α)) r) (Ici 1) :=
      continuousOn_id.div hVc.continuousOn
        (fun r hr => (hVpos r (lt_of_lt_of_le one_pos hr)).ne')
    exact h.congr (fun r hr => by
      rw [weightedBallVolume_eq_cumulativeArea volume hw (le_trans zero_le_one hr)])
  have hsplit : Ici (1:ℝ) = Icc 1 64 ∪ Ioi 64 := (Icc_union_Ioi_eq_Ici (by norm_num)).symm
  rw [hsplit]
  apply IntegrableOn.union
  · exact (hcont.mono Icc_subset_Ici_self).integrableOn_Icc
  · have hb : IntegrableOn (fun r : ℝ => c⁻¹ * r ^ (-2:ℝ)) (Ioi 64) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    apply Integrable.mono' hb
    · have hIoi : Ioi (64:ℝ) ⊆ Ici 1 := fun r hr =>
        le_of_lt (lt_trans (by norm_num : (1:ℝ) < 64) hr)
      exact (hcont.mono hIoi).aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all
      intro r hr
      have hr0 : (0:ℝ) < r := lt_trans (by norm_num) hr
      have hV := hlow r hr.le
      have hVpos' : 0 < weightedBallVolume volume (latticeWeight latticeValleys α) r :=
        lt_of_lt_of_le (by positivity) hV
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr0.le hVpos'.le),
        Real.rpow_neg hr0.le, Real.rpow_two, div_le_iff₀ hVpos']
      calc r = c⁻¹ * (r^2)⁻¹ * (c * r^3) := by field_simp
        _ ≤ c⁻¹ * (r^2)⁻¹ * weightedBallVolume volume (latticeWeight latticeValleys α) r := by
          gcongr

/-! ### Thin shells: one layer of circles per shell -/

theorem latticeCircleRadius_sub (k : ℕ) {i i' : Fin (latticeLayerCount k)}
    (h : i.val < i'.val) :
    (2:ℝ)^k / latticeLayerCount k ≤ latticeCircleRadius k i' - latticeCircleRadius k i := by
  have hi' : (i.val:ℝ)+1 ≤ i'.val := by exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_right hi'
    (by positivity : 0 ≤ (2:ℝ)^k/latticeLayerCount k)
  unfold latticeCircleRadius
  linarith

/-- The layer of shell `k` whose radius lies in the window `(lo, hi)`, if any. -/
noncomputable def windowLayer (k : ℕ) (lo hi : ℝ) : Fin (latticeLayerCount k) :=
  if h : ∃ i : Fin (latticeLayerCount k),
      lo < latticeCircleRadius k i ∧ latticeCircleRadius k i < hi
  then h.choose else ⟨0, by unfold latticeLayerCount; positivity⟩

/-- A radial window no longer than the mesh contains at most one layer. -/
theorem windowLayer_unique {k : ℕ} {lo hi : ℝ}
    (hmesh : hi - lo ≤ (2:ℝ)^k / latticeLayerCount k) {i : Fin (latticeLayerCount k)}
    (h1 : lo < latticeCircleRadius k i) (h2 : latticeCircleRadius k i < hi) :
    i = windowLayer k lo hi := by
  have hex : ∃ i : Fin (latticeLayerCount k),
      lo < latticeCircleRadius k i ∧ latticeCircleRadius k i < hi := ⟨i, h1, h2⟩
  unfold windowLayer
  rw [dif_pos hex]
  obtain ⟨h3, h4⟩ := hex.choose_spec
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · have := latticeCircleRadius_sub k h
    linarith
  · have := latticeCircleRadius_sub k h
    linarith

/-- Points of the thin shell `[r, r+ρ)` closer than `3ρ` to the valleys. -/
def thinBad (r ρ : ℝ) : Set LatticeSpace :=
  {x | r ≤ ‖x‖ ∧ ‖x‖ < r + ρ ∧ infDist x latticeValleys < 3*ρ}

/-- Points of the thin shell `[r, r+ρ)` at distance at least `3ρ` from the valleys. -/
def thinGood (r ρ : ℝ) : Set LatticeSpace :=
  {x | r ≤ ‖x‖ ∧ ‖x‖ < r + ρ ∧ 3*ρ ≤ infDist x latticeValleys}

theorem thinGood_measurable (r ρ : ℝ) : MeasurableSet (thinGood r ρ) := by
  have hn : Measurable (fun x : LatticeSpace => ‖x‖) := measurable_norm
  have hd : Measurable (fun x : LatticeSpace => infDist x latticeValleys) :=
    (continuous_infDist_pt _).measurable
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_lt hn measurable_const).inter (measurableSet_le measurable_const hd))

theorem thinBad_subset {k n : ℕ} (hk : 5 ≤ k) (hn : 0 < n) {r ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hr1 : (2:ℝ)^k ≤ r) (hr2 : r < (2:ℝ)^(k+1)) (hρ : 14*ρ ≤ (2:ℝ)^(k/2))
    (hnρ : (2:ℝ)^(k+2) * Real.pi / n ≤ ρ) :
    thinBad r ρ ⊆ ⋃ m : Fin 3, ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ⋃ l : Fin n,
      ball (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l)
        (4*ρ) := by
  rintro x ⟨hx1, hx2, hx3⟩
  obtain ⟨y, hy, hd⟩ := (infDist_lt_iff latticeValleys_nonempty).mp hx3
  obtain ⟨⟨k', hk'⟩, hy⟩ := mem_iUnion.mp hy
  obtain ⟨i, hy⟩ := mem_iUnion.mp hy
  obtain ⟨j, hy⟩ := mem_iUnion.mp hy
  dsimp only at i j hy
  obtain ⟨hab, hale, hb2⟩ := lattice_half_powers k
  have hb1 : (1:ℝ) ≤ (2:ℝ)^((k+1)/2) := one_le_pow₀ (by norm_num)
  have hapos : 0 < (2:ℝ)^(k/2) := by positivity
  have haT : (2:ℝ)^(k/2) ≤ (2:ℝ)^k := by nlinarith
  have hp1 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
  have hp2 : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_add]; ring
  have hpm : (2:ℝ)^(k-1) = (2:ℝ)^k/2 := by
    have : (2:ℝ)^k = 2 * 2^(k-1) := by
      rw [← pow_succ']
      congr 1
      omega
    linarith
  have hloc := lattice_shell_localization i j (by omega) (hr1.trans hx1)
    (by linarith) (by linarith) hd hy
  obtain ⟨m, rfl⟩ : ∃ m : Fin 3, k' = k - 1 + m.val :=
    ⟨⟨k' - (k-1), by omega⟩, by simp only; omega⟩
  have hyR : ‖y‖ = latticeCircleRadius (k-1+m.val) i := hy.1
  have hnorm : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  obtain ⟨hn1, hn2⟩ := abs_le.mp hnorm
  have hmesh : (r+4*ρ) - (r-3*ρ) ≤ (2:ℝ)^(k-1+m.val) / latticeLayerCount (k-1+m.val) := by
    rw [lattice_radial_mesh]
    have h1 : (2:ℝ)^((k-1)/2) ≤ (2:ℝ)^((k-1+m.val)/2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2:ℝ)^(k/2) ≤ 2 * (2:ℝ)^((k-1)/2) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hi : i = windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ) :=
    windowLayer_unique hmesh (by rw [← hyR]; linarith) (by rw [← hyR]; linarith)
  subst hi
  obtain ⟨l, hl⟩ := indexedLatticeCircle_cover _ _ j hn hy
  simp only [mem_iUnion, mem_ball]
  refine ⟨m, j, l, ?_⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hle : (2:ℝ)^(k-1+m.val+1) * Real.pi / n ≤ ρ := by
    refine le_trans ?_ hnρ
    have hpi := Real.pi_pos
    have : (2:ℝ)^(k-1+m.val+1) ≤ (2:ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  calc dist x (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l)
      ≤ dist x y + dist y
          (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l) :=
        dist_triangle _ _ _
    _ < 3*ρ + ρ := add_lt_add_of_lt_of_le hd (hl.trans hle)
    _ = 4*ρ := by ring

theorem thinBad_volume_le {k n : ℕ} (hk : 5 ≤ k) (hn : 0 < n) {r ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hr1 : (2:ℝ)^k ≤ r) (hr2 : r < (2:ℝ)^(k+1)) (hρ : 14*ρ ≤ (2:ℝ)^(k/2))
    (hnρ : (2:ℝ)^(k+2) * Real.pi / n ≤ ρ) :
    volume.real (thinBad r ρ) ≤
      3 * (2:ℝ)^(2+(k+1)/2) * n * (4/3 * Real.pi * (4*ρ)^3) := by
  have hsub := thinBad_subset hk hn hρ0 hr1 hr2 hρ hnρ
  have hfin : volume (⋃ m : Fin 3, ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)),
      ⋃ l : Fin n,
        ball (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l)
          (4*ρ)) ≠ ∞ := by
    apply (Bornology.IsBounded.measure_lt_top _).ne
    simp only [Bornology.isBounded_iUnion, isBounded_ball, implies_true]
  refine (measureReal_mono hsub hfin).trans ?_
  have h4ρ : 0 ≤ 4*ρ := by positivity
  calc volume.real (⋃ m : Fin 3, ⋃ j : Fin (latticeCirclesPerLayer (k-1+m.val)),
        ⋃ l : Fin n,
          ball (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l)
            (4*ρ))
      ≤ ∑ m : Fin 3, ∑ j : Fin (latticeCirclesPerLayer (k-1+m.val)), ∑ l : Fin n,
          volume.real (ball
            (coverCenter (k-1+m.val) n (windowLayer (k-1+m.val) (r-3*ρ) (r+4*ρ)) j l)
            (4*ρ)) := by
        refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun m _ => ?_)
        refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact measureReal_iUnion_fintype_le _
    _ = ∑ m : Fin 3, (latticeCirclesPerLayer (k-1+m.val) : ℝ) * n *
          (4/3 * Real.pi * (4*ρ)^3) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [lattice_ball_volume_real _ h4ρ, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ∑ _m : Fin 3, (2:ℝ)^(2+(k+1)/2) * n * (4/3 * Real.pi * (4*ρ)^3) := by
        apply Finset.sum_le_sum
        intro m _
        have hpi := Real.pi_pos
        have hM : (latticeCirclesPerLayer (k-1+m.val) : ℝ) ≤ (2:ℝ)^(2+(k+1)/2) := by
          unfold latticeCirclesPerLayer
          push_cast
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        gcongr
    _ = 3 * (2:ℝ)^(2+(k+1)/2) * n * (4/3 * Real.pi * (4*ρ)^3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- At least half of every thin shell of thickness `2^(k/2)/8192` stays three
thicknesses away from the valleys. -/
theorem thinGood_volume_ge {k : ℕ} (hk : 5 ≤ k) {r : ℝ}
    (hr1 : (2:ℝ)^k ≤ r) (hr2 : r < (2:ℝ)^(k+1)) :
    2/3 * Real.pi * ((r + (2:ℝ)^(k/2)/8192)^3 - r^3) ≤
      volume.real (thinGood r ((2:ℝ)^(k/2)/8192)) := by
  obtain ⟨hab, hale, hb2⟩ := lattice_half_powers k
  have hpi := Real.pi_pos
  have hapos : 0 < (2:ℝ)^(k/2) := by positivity
  have hb1 : (1:ℝ) ≤ (2:ℝ)^((k+1)/2) := one_le_pow₀ (by norm_num)
  have hTpos : 0 < (2:ℝ)^k := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le hTpos hr1
  have hpow2 : (2:ℝ)^(k+2) = 4*(2:ℝ)^k := by rw [pow_add]; ring
  have hn : 0 < 2^(17+(k+1)/2) := by positivity
  have hncast : ((2^(17+(k+1)/2) : ℕ) : ℝ) = 131072 * (2:ℝ)^((k+1)/2) := by
    push_cast
    rw [pow_add]
    norm_num
  have hMcast : (2:ℝ)^(2+(k+1)/2) = 4 * (2:ℝ)^((k+1)/2) := by
    rw [pow_add]
    norm_num
  have hbad := thinBad_volume_le hk hn (r := r) (ρ := (2:ℝ)^(k/2)/8192) (by positivity)
    hr1 hr2 (by linarith)
    (by
      rw [hncast, div_le_iff₀ (by positivity), hpow2]
      nlinarith [Real.pi_le_four])
  have hbad' : volume.real (thinBad r ((2:ℝ)^(k/2)/8192)) ≤
      2 * Real.pi * r^2 * ((2:ℝ)^(k/2)/8192) := by
    refine hbad.trans ?_
    rw [hncast, hMcast]
    have e : 3 * (4 * (2:ℝ)^((k+1)/2)) * (131072 * (2:ℝ)^((k+1)/2)) *
        (4/3 * Real.pi * (4*((2:ℝ)^(k/2)/8192))^3) =
        2 * Real.pi * ((2:ℝ)^(k/2) * (2:ℝ)^((k+1)/2))^2 * ((2:ℝ)^(k/2)/8192) := by ring
    rw [e, hab]
    have hsq : ((2:ℝ)^k)^2 ≤ r^2 := pow_le_pow_left₀ hTpos.le hr1 2
    gcongr
  have hsup : ball (0:LatticeSpace) r ∪
      (thinBad r ((2:ℝ)^(k/2)/8192) ∪ thinGood r ((2:ℝ)^(k/2)/8192)) ⊆
      ball (0:LatticeSpace) (r + (2:ℝ)^(k/2)/8192) := by
    rintro x (h | ⟨_, h, _⟩ | ⟨_, h, _⟩)
    · rw [mem_ball_zero_iff] at h ⊢
      linarith
    · rwa [mem_ball_zero_iff]
    · rwa [mem_ball_zero_iff]
  have hcov : ball (0:LatticeSpace) (r + (2:ℝ)^(k/2)/8192) ⊆ ball (0:LatticeSpace) r ∪
      (thinBad r ((2:ℝ)^(k/2)/8192) ∪ thinGood r ((2:ℝ)^(k/2)/8192)) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases h1 : ‖x‖ < r
    · left
      rwa [mem_ball_zero_iff]
    · right
      by_cases h2 : infDist x latticeValleys < 3*((2:ℝ)^(k/2)/8192)
      · left
        exact ⟨not_lt.mp h1, hx, h2⟩
      · right
        exact ⟨not_lt.mp h1, hx, not_lt.mp h2⟩
  have hbig := (measureReal_mono hcov
    (measure_ne_top_of_subset hsup (measure_ball_lt_top (μ := (volume : Measure LatticeSpace))
      (x := 0) (r := r + (2:ℝ)^(k/2)/8192)).ne)).trans
      ((measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _))
  rw [lattice_ball_volume_real _ (by positivity), lattice_ball_volume_real _ hrpos.le] at hbig
  have hcube : 3 * r^2 * ((2:ℝ)^(k/2)/8192) ≤ (r + (2:ℝ)^(k/2)/8192)^3 - r^3 := by
    have hρ : 0 < (2:ℝ)^(k/2)/8192 := by positivity
    nlinarith [mul_pos hrpos hρ, mul_pos (mul_pos hrpos hρ) hρ, pow_pos hρ 3]
  nlinarith [mul_le_mul_of_nonneg_left hcube hpi.le]

/-! ### Sphere means -/

/-- A continuous cutoff: zero within `2ρ` of the valleys, one beyond `3ρ`. -/
noncomputable def valleyCutoff (ρ : ℝ) (x : LatticeSpace) : ℝ :=
  min 1 (max 0 (infDist x latticeValleys / ρ - 2))

theorem valleyCutoff_continuous (ρ : ℝ) : Continuous (valleyCutoff ρ) := by
  have hd : Continuous (fun x : LatticeSpace => infDist x latticeValleys) :=
    continuous_infDist_pt _
  exact continuous_const.min (continuous_const.max ((hd.div_const ρ).sub continuous_const))

theorem valleyCutoff_nonneg (ρ : ℝ) (x : LatticeSpace) : 0 ≤ valleyCutoff ρ x :=
  le_min zero_le_one (le_max_left _ _)

theorem valleyCutoff_le_one (ρ : ℝ) (x : LatticeSpace) : valleyCutoff ρ x ≤ 1 :=
  min_le_left _ _

theorem valleyCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {x : LatticeSpace}
    (hx : 3*ρ ≤ infDist x latticeValleys) : valleyCutoff ρ x = 1 := by
  unfold valleyCutoff
  apply min_eq_left
  apply le_max_of_le_right
  rw [le_sub_iff_add_le, le_div_iff₀ hρ]
  linarith

theorem valleyCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {x : LatticeSpace}
    (hx : infDist x latticeValleys ≤ 2*ρ) : valleyCutoff ρ x = 0 := by
  unfold valleyCutoff
  have h : infDist x latticeValleys / ρ - 2 ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hρ]
    exact hx
  rw [max_eq_left h]
  exact min_eq_right zero_le_one

/-- Radial comparison: the weight at radius `r` dominates the cutoff at any
radius within `ρ`, in the same direction. -/
theorem latticeWeight_ge_cutoff {α : ℝ} (hα : 0 ≤ α) {k : ℕ} {x y : LatticeSpace}
    (hx : ‖x‖ < (2:ℝ)^(k+1)) (hxy : dist x y ≤ (2:ℝ)^(k/2)/8192) :
    (1/268435457 : ℝ)^(α/2) * valleyCutoff ((2:ℝ)^(k/2)/8192) y ≤
      latticeWeight latticeValleys α x := by
  have hρ : 0 < (2:ℝ)^(k/2)/8192 := by positivity
  have hc : 0 ≤ (1/268435457 : ℝ)^(α/2) := by positivity
  by_cases hy : infDist y latticeValleys ≤ 2*((2:ℝ)^(k/2)/8192)
  · rw [valleyCutoff_eq_zero hρ hy, mul_zero]
    exact (latticeWeight_pos _ _ x).le
  · have hy' := not_le.mp hy
    have hd : infDist y latticeValleys ≤ infDist x latticeValleys + dist y x :=
      infDist_le_infDist_add_dist
    rw [dist_comm] at hd
    have hdx : (2:ℝ)^(k/2)/8192 ≤ infDist x latticeValleys := by linarith
    refine le_trans (mul_le_of_le_one_right hc (valleyCutoff_le_one _ y)) ?_
    obtain ⟨hab, hale, hb2⟩ := lattice_half_powers k
    apply latticeWeight_lower _ hα (by norm_num)
    have hapos : 0 < (2:ℝ)^(k/2) := by positivity
    have hdsq : ((2:ℝ)^(k/2)/8192)^2 ≤ (infDist x latticeValleys)^2 :=
      pow_le_pow_left₀ hρ.le hdx 2
    have he : ((2:ℝ)^(k/2)/8192)^2 = ((2:ℝ)^(k/2))^2/67108864 := by ring
    rw [he] at hdsq
    have hT : (2:ℝ)^k ≤ 2 * ((2:ℝ)^(k/2))^2 := by nlinarith
    rw [pow_succ] at hx
    linarith

theorem lattice_finrank_sub_one : Module.finrank ℝ LatticeSpace - 1 = 2 := by
  simp [LatticeSpace]

theorem lattice_sphere_slice_integrable {f : LatticeSpace → ℝ} (hf : Continuous f) (r : ℝ) :
    Integrable (fun θ : sphere (0 : LatticeSpace) 1 => f (r • θ.val))
      (volume : Measure LatticeSpace).toSphere := by
  have hc : Continuous (fun θ : sphere (0 : LatticeSpace) 1 => f (r • θ.val)) := by fun_prop
  simpa using hc.continuousOn.integrableOn_compact
    (μ := (volume : Measure LatticeSpace).toSphere) isCompact_univ

/-- The mass of the cutoff in a thin shell dominates the good volume. -/
theorem thinGood_volume_le_cutoff {r ρ : ℝ} (hρ : 0 < ρ) :
    volume.real (thinGood r ρ) ≤
      weightedBallVolume volume (valleyCutoff ρ) (r + ρ) -
        weightedBallVolume volume (valleyCutoff ρ) r := by
  unfold weightedBallVolume
  have hφ := valleyCutoff_continuous ρ
  have hi : IntegrableOn (valleyCutoff ρ) (ball (0 : LatticeSpace) (r + ρ)) volume :=
    (hφ.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LatticeSpace) (r + ρ))).mono_set ball_subset_closedBall
  rw [← integral_diff measurableSet_ball hi (ball_subset_ball (by linarith))]
  have hsub : thinGood r ρ ⊆ ball (0 : LatticeSpace) (r + ρ) \ ball (0 : LatticeSpace) r :=
    fun x hx => ⟨by rw [mem_ball_zero_iff]; exact hx.2.1,
      by rw [mem_ball_zero_iff]; exact not_lt.mpr hx.1⟩
  have hfin : volume (thinGood r ρ) ≠ ∞ :=
    measure_ne_top_of_subset (hsub.trans diff_subset)
      (measure_ball_lt_top (μ := (volume : Measure LatticeSpace)) (x := 0) (r := r + ρ)).ne
  calc volume.real (thinGood r ρ) = ∫ _x in thinGood r ρ, (1:ℝ) := by
        rw [setIntegral_const, smul_eq_mul, mul_one]
    _ = ∫ x in thinGood r ρ, valleyCutoff ρ x :=
        setIntegral_congr_fun (thinGood_measurable _ _)
          (fun x hx => (valleyCutoff_eq_one hρ hx.2.2).symm)
    _ ≤ ∫ x in ball (0 : LatticeSpace) (r + ρ) \ ball (0 : LatticeSpace) r, valleyCutoff ρ x :=
        setIntegral_mono_set (hi.mono_set diff_subset)
          (ae_of_all _ (valleyCutoff_nonneg ρ)) hsub.eventuallyLE

/-- Uniform lower bound for the unnormalized sphere mean on every sphere of
shell `k ≥ 5`. -/
theorem lattice_sphere_mean_shell {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 5 ≤ k) {r : ℝ}
    (hr1 : (2:ℝ)^k ≤ r) (hr2 : r < (2:ℝ)^(k+1)) :
    (1/268435457 : ℝ)^(α/2) * (2 * Real.pi) ≤
      ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
        ∂(volume : Measure LatticeSpace).toSphere := by
  have hpi := Real.pi_pos
  have hρ : 0 < (2:ℝ)^(k/2)/8192 := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hw := latticeWeight_continuous latticeValleys α
  have hφ := valleyCutoff_continuous ((2:ℝ)^(k/2)/8192)
  have hc : 0 ≤ (1/268435457 : ℝ)^(α/2) := by positivity
  have hle : r ≤ r + (2:ℝ)^(k/2)/8192 := by linarith
  have h1 : ∀ s ∈ Icc r (r + (2:ℝ)^(k/2)/8192),
      (1/268435457 : ℝ)^(α/2) *
          sphericalArea volume (valleyCutoff ((2:ℝ)^(k/2)/8192)) s ≤
        s^2 * ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere := by
    intro s hs
    have hmono : (∫ θ : sphere (0 : LatticeSpace) 1, (1/268435457 : ℝ)^(α/2) *
          valleyCutoff ((2:ℝ)^(k/2)/8192) (s • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere) ≤
        ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere := by
      apply integral_mono ((lattice_sphere_slice_integrable hφ s).const_mul _)
        (lattice_sphere_slice_integrable hw r)
      intro θ
      have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
      apply latticeWeight_ge_cutoff hα
      · rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
        exact hr2
      · rw [dist_eq_norm, ← sub_smul, norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hs.1, hs.2]
    rw [integral_const_mul] at hmono
    unfold sphericalArea
    rw [lattice_finrank_sub_one]
    calc (1/268435457 : ℝ)^(α/2) * (s^2 * ∫ θ : sphere (0 : LatticeSpace) 1,
          valleyCutoff ((2:ℝ)^(k/2)/8192) (s • θ.val) ∂(volume : Measure LatticeSpace).toSphere)
        = s^2 * ((1/268435457 : ℝ)^(α/2) * ∫ θ : sphere (0 : LatticeSpace) 1,
          valleyCutoff ((2:ℝ)^(k/2)/8192) (s • θ.val)
            ∂(volume : Measure LatticeSpace).toSphere) := by ring
      _ ≤ s^2 * ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg s)
  have hAφ := sphericalArea_continuous volume hφ
  have h2 := intervalIntegral.integral_mono_on (μ := volume) hle
    ((continuous_const.mul hAφ).intervalIntegrable _ _)
    (((continuous_pow 2).mul continuous_const).intervalIntegrable _ _) h1
  have hint : (∫ s in r..(r + (2:ℝ)^(k/2)/8192), s^2) =
      ((r + (2:ℝ)^(k/2)/8192)^3 - r^3)/3 := by
    rw [integral_pow]
    norm_num
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, hint] at h2
  have h3 : (∫ s in r..(r + (2:ℝ)^(k/2)/8192),
      sphericalArea volume (valleyCutoff ((2:ℝ)^(k/2)/8192)) s) =
      weightedBallVolume volume (valleyCutoff ((2:ℝ)^(k/2)/8192)) (r + (2:ℝ)^(k/2)/8192) -
        weightedBallVolume volume (valleyCutoff ((2:ℝ)^(k/2)/8192)) r := by
    rw [weightedBallVolume_eq_cumulativeArea volume hφ (by linarith),
      weightedBallVolume_eq_cumulativeArea volume hφ hrpos.le]
    unfold cumulativeArea
    exact (intervalIntegral.integral_interval_sub_left (hAφ.intervalIntegrable _ _)
      (hAφ.intervalIntegrable _ _)).symm
  have h4 := thinGood_volume_le_cutoff (r := r) hρ
  have h5 := thinGood_volume_ge hk hr1 hr2
  rw [h3] at h2
  have hD : 0 < ((r + (2:ℝ)^(k/2)/8192)^3 - r^3)/3 := by
    have : r^3 < (r + (2:ℝ)^(k/2)/8192)^3 := pow_lt_pow_left₀ (by linarith) hrpos.le (by norm_num)
    linarith
  have h6 : ((r + (2:ℝ)^(k/2)/8192)^3 - r^3)/3 * ((1/268435457 : ℝ)^(α/2) * (2 * Real.pi)) ≤
      ((r + (2:ℝ)^(k/2)/8192)^3 - r^3)/3 *
        ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere := by
    refine le_trans ?_ h2
    have h7 := mul_le_mul_of_nonneg_left (h5.trans h4) hc
    linarith
  exact le_of_mul_le_mul_left h6 hD

/-- Sphere half of `thm:B`(b): the spherical area of the lattice weight grows
quadratically, i.e. the sphere mean is bounded below, for `r ≥ 16`. -/
theorem lattice_sphere_mean_lower {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 16 ≤ r →
      c * r^2 ≤ sphericalArea volume (latticeWeight latticeValleys α) r := by
  have hw := latticeWeight_continuous latticeValleys α
  have hp : ∀ x, 0 < latticeWeight latticeValleys α x := latticeWeight_pos _ _
  have hAc := sphericalArea_continuous volume hw
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (16:ℝ) ≤ 32)) hAc.continuousOn
  obtain ⟨m, hmpos, hmin'⟩ : ∃ m : ℝ, 0 < m ∧ ∀ r ∈ Icc (16:ℝ) 32,
      m ≤ sphericalArea volume (latticeWeight latticeValleys α) r :=
    ⟨_, sphericalArea_pos volume hw hp (lt_of_lt_of_le (by norm_num) hr₀.1),
      isMinOn_iff.mp hmin⟩
  have hpi := Real.pi_pos
  have hc0 : 0 < (1/268435457 : ℝ)^(α/2) := by positivity
  refine ⟨min ((1/268435457 : ℝ)^(α/2) * (2 * Real.pi)) (m/1024),
    lt_min (by positivity) (by positivity), ?_⟩
  intro r hr
  have hr2nn : 0 ≤ r^2 := sq_nonneg r
  by_cases h32 : r ≤ 32
  · have hsq : r^2 ≤ 1024 := by nlinarith
    calc min ((1/268435457 : ℝ)^(α/2) * (2 * Real.pi)) (m/1024) * r^2
        ≤ m/1024 * r^2 := mul_le_mul_of_nonneg_right (min_le_right _ _) hr2nn
      _ ≤ m/1024 * 1024 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = m := by ring
      _ ≤ sphericalArea volume (latticeWeight latticeValleys α) r := hmin' r ⟨hr, h32⟩
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1:ℝ) ≤ r)
      (by norm_num : (1:ℝ) < 2)
    have hn5 : 5 ≤ n := by
      by_contra h
      have h5 : n + 1 ≤ 5 := by omega
      have h32' : (2:ℝ)^(n+1) ≤ (2:ℝ)^5 := pow_le_pow_right₀ (by norm_num) h5
      have e : (2:ℝ)^5 = 32 := by norm_num
      linarith
    have h := lattice_sphere_mean_shell hα hn5 hn1 hn2
    unfold sphericalArea
    rw [lattice_finrank_sub_one]
    calc min ((1/268435457 : ℝ)^(α/2) * (2 * Real.pi)) (m/1024) * r^2
        ≤ ((1/268435457 : ℝ)^(α/2) * (2 * Real.pi)) * r^2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr2nn
      _ ≤ (∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere) * r^2 :=
          mul_le_mul_of_nonneg_right h hr2nn
      _ = r^2 * ∫ θ : sphere (0 : LatticeSpace) 1, latticeWeight latticeValleys α (r • θ.val)
          ∂(volume : Measure LatticeSpace).toSphere := mul_comm _ _

/-- Brown's sphere integral converges for the lattice weight: the sphere test
is silent (`thm:B`(b), first half). -/
theorem lattice_sphere_integral_converges {α : ℝ} (hα : 0 ≤ α) :
    IntegrableOn (fun r => 1 / sphericalArea volume (latticeWeight latticeValleys α) r)
      (Ici 1) := by
  have hw := latticeWeight_continuous latticeValleys α
  have hp : ∀ x, 0 < latticeWeight latticeValleys α x := latticeWeight_pos _ _
  have hAc := sphericalArea_continuous volume hw
  obtain ⟨c, hc, hlow⟩ := lattice_sphere_mean_lower hα
  have hcont : ContinuousOn
      (fun r => 1 / sphericalArea volume (latticeWeight latticeValleys α) r) (Ici 1) :=
    continuousOn_const.div hAc.continuousOn
      (fun r hr => (sphericalArea_pos volume hw hp (lt_of_lt_of_le one_pos hr)).ne')
  have hsplit : Ici (1:ℝ) = Icc 1 16 ∪ Ioi 16 := (Icc_union_Ioi_eq_Ici (by norm_num)).symm
  rw [hsplit]
  apply IntegrableOn.union
  · exact (hcont.mono Icc_subset_Ici_self).integrableOn_Icc
  · have hb : IntegrableOn (fun r : ℝ => c⁻¹ * r ^ (-2:ℝ)) (Ioi 16) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    apply Integrable.mono' hb
    · have hIoi : Ioi (16:ℝ) ⊆ Ici 1 := fun r hr =>
        le_of_lt (lt_trans (by norm_num : (1:ℝ) < 16) hr)
      exact (hcont.mono hIoi).aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all
      intro r hr
      have hr0 : (0:ℝ) < r := lt_trans (by norm_num) hr
      have hA := hlow r hr.le
      have hApos : 0 < sphericalArea volume (latticeWeight latticeValleys α) r :=
        lt_of_lt_of_le (by positivity) hA
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hApos.le),
        Real.rpow_neg hr0.le, Real.rpow_two, div_le_iff₀ hApos]
      calc (1:ℝ) = c⁻¹ * (r^2)⁻¹ * (c * r^2) := by field_simp
        _ ≤ c⁻¹ * (r^2)⁻¹ * sphericalArea volume (latticeWeight latticeValleys α) r := by
          gcongr

end BrownRadial
