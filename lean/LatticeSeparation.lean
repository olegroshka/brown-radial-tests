import LatticeGeometry
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Quantitative separation of the lattice circles used in the proof of
`thm:B`(a): coaxial circles are at least as far apart as their meridian
points, circles of one layer are at least `0.78 L_k` apart, and two distinct
circles of one shell are at least `0.7 s_k` apart, where `s_k = sqrt (2^k)`.
These are separation statements only; no doubling or Poincare inequality is
claimed here.
-/

open Set Metric
namespace BrownRadial

theorem euclidean3_dist_sq (x y : LatticeSpace) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem euclidean3_norm_sq (x : LatticeSpace) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- The horizontal (cylindrical) radius of a latitude circle. -/
theorem latitudeCircle_horizontal_sq {R θ : ℝ} {x : LatticeSpace}
    (hx : x ∈ latitudeCircle R θ) :
    (x 0) ^ 2 + (x 1) ^ 2 = (R * Real.sin θ) ^ 2 := by
  have hn := euclidean3_norm_sq x
  rw [hx.1, hx.2] at hn
  linear_combination (-1 : ℝ) * hn - R ^ 2 * (Real.sin_sq_add_cos_sq θ)

/-- Two coaxial latitude circles are at least as far apart as their
generating points in a common meridian half-plane. -/
theorem latitudeCircle_dist_sq_ge {R R' θ θ' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hθ : 0 ≤ Real.sin θ) (hθ' : 0 ≤ Real.sin θ') {x y : LatticeSpace}
    (hx : x ∈ latitudeCircle R θ) (hy : y ∈ latitudeCircle R' θ') :
    R ^ 2 + R' ^ 2 - 2 * R * R' * Real.cos (θ - θ') ≤ dist x y ^ 2 := by
  have hxh := latitudeCircle_horizontal_sq hx
  have hyh := latitudeCircle_horizontal_sq hy
  have hcs : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (R * Real.sin θ * (R' * Real.sin θ')) ^ 2 := by
    rw [mul_pow, ← hxh, ← hyh]
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have hle : x 0 * y 0 + x 1 * y 1 ≤ R * Real.sin θ * (R' * Real.sin θ') :=
    (abs_le_of_sq_le_sq' hcs (mul_nonneg (mul_nonneg hR hθ) (mul_nonneg hR' hθ'))).2
  have h1 : R ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = R ^ 2 := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  have h2 : R' ^ 2 * (Real.sin θ' ^ 2 + Real.cos θ' ^ 2) = R' ^ 2 := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  have e1 : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 =
      (R * Real.sin θ) ^ 2 + (R' * Real.sin θ') ^ 2 - 2 * (x 0 * y 0 + x 1 * y 1) := by
    rw [← hxh, ← hyh]
    ring
  rw [euclidean3_dist_sq, e1, hx.2, hy.2, Real.cos_sub]
  nlinarith [h1, h2, hle]

/-- Circles in one layer have polar angles differing by at least one layer
step `pi L_k / N_k`. -/
theorem lattice_same_layer_angle_gap (k : ℕ) (i : Fin (latticeLayerCount k))
    {j j' : Fin (latticeCirclesPerLayer k)} (hj : j ≠ j') :
    Real.pi * latticeLayerCount k / latticeCircleCount k ≤
      |latticePolarAngle k (latticeAngleIndex k (i, j)) -
        latticePolarAngle k (latticeAngleIndex k (i, j'))| := by
  have hN : (0 : ℝ) < latticeCircleCount k := by unfold latticeCircleCount; positivity
  have hL : (0 : ℝ) < latticeLayerCount k := by unfold latticeLayerCount; positivity
  have hjj : (1 : ℝ) ≤ |(j.val : ℝ) - j'.val| := by
    have hne : (j.val : ℤ) - j'.val ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      omega
    have h1 : (1 : ℤ) ≤ |(j.val : ℤ) - j'.val| := Int.one_le_abs hne
    exact_mod_cast h1
  have he : latticePolarAngle k (latticeAngleIndex k (i, j)) -
      latticePolarAngle k (latticeAngleIndex k (i, j')) =
      (Real.pi * latticeLayerCount k / latticeCircleCount k) * ((j.val : ℝ) - j'.val) := by
    unfold latticePolarAngle
    rw [latticeAngleIndex_val, latticeAngleIndex_val]
    push_cast
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos (by positivity)]
  exact le_mul_of_one_le_right (by positivity) hjj

theorem latticeCircleCount_cast (k : ℕ) : (latticeCircleCount k : ℝ) = 4 * (2 : ℝ) ^ k := by
  simp [latticeCircleCount, pow_add]
  ring

/-- From shell four on there are at least sixteen circles in each layer. -/
theorem lattice_layer_count_le (k : ℕ) (hk : 4 ≤ k) :
    (latticeLayerCount k : ℝ) * 16 ≤ latticeCircleCount k := by
  have h : latticeLayerCount k * 16 ≤ latticeCircleCount k := by
    unfold latticeLayerCount latticeCircleCount
    calc
      2 ^ ((k + 1) / 2) * 16 = 2 ^ ((k + 1) / 2 + 4) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h

/-- The layer step angle is positive and small from shell four on. -/
theorem same_layer_delta_small {p L N P δ : ℝ} (hL : 0 < L) (hp : 0 < p)
    (hN : N = 4 * p) (hLN : L * 16 ≤ N)
    (hP3 : (157 / 50 : ℝ) < P) (hP4 : P < (63 / 20 : ℝ)) (hδ : δ = P * L / N) :
    0 < δ ∧ δ ≤ 1 / 5 := by
  have hNpos : 0 < N := by rw [hN]; positivity
  have hPpos : 0 < P := by linarith
  constructor
  · rw [hδ]; positivity
  · rw [hδ, div_le_iff₀ hNpos]
    have h := mul_lt_mul_of_pos_right hP4 hL
    linarith

/-- Scalar arithmetic behind the same-layer bound. -/
theorem same_layer_arith {R p L N P δ c D2 : ℝ} (hL : 0 < L) (hp : 0 < p)
    (hN : N = 4 * p) (hLN : L * 16 ≤ N) (hR : p ≤ R)
    (hP3 : (157 / 50 : ℝ) < P) (hP4 : P < (63 / 20 : ℝ)) (hδ : δ = P * L / N)
    (hc : c ≤ 1 - δ ^ 2 / 2 + δ ^ 4 * (5 / 96))
    (hD : R ^ 2 * (2 - 2 * c) ≤ D2) :
    ((78 / 100 : ℝ) * L) ^ 2 ≤ D2 := by
  obtain ⟨hδpos, hδsmall⟩ := same_layer_delta_small hL hp hN hLN hP3 hP4 hδ
  have hδsq : δ ^ 2 ≤ 1 / 25 := by
    calc
      δ ^ 2 = δ * δ := sq δ
      _ ≤ (1 / 5) * (1 / 5) := mul_le_mul hδsmall hδsmall hδpos.le (by norm_num)
      _ = 1 / 25 := by norm_num
  have h4 : δ ^ 4 ≤ δ ^ 2 * (1 / 25) := by
    have h3 : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hδsq (sq_nonneg _)
  have h2 : δ ^ 2 * (239 / 240 : ℝ) ≤ 2 - 2 * c := by linarith
  have hRδ : (157 / 200 : ℝ) * L ≤ R * δ := by
    have he : p * δ = P / 4 * L := by
      rw [hδ, hN]
      field_simp
    have h1 : p * δ ≤ R * δ := mul_le_mul_of_nonneg_right hR hδpos.le
    have h2' := mul_lt_mul_of_pos_right hP3 hL
    linarith
  have hsq : ((157 / 200 : ℝ) * L) ^ 2 ≤ (R * δ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRδ 2
  have hmul : R ^ 2 * (δ ^ 2 * (239 / 240)) ≤ R ^ 2 * (2 - 2 * c) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg R)
  have hnum : ((78 / 100 : ℝ)) ^ 2 ≤ (239 / 240) * (157 / 200) ^ 2 := by norm_num
  calc
    ((78 / 100 : ℝ) * L) ^ 2 = (78 / 100) ^ 2 * L ^ 2 := by ring
    _ ≤ ((239 / 240) * (157 / 200) ^ 2) * L ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg L)
    _ = (239 / 240) * ((157 / 200 : ℝ) * L) ^ 2 := by ring
    _ ≤ (239 / 240) * (R * δ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = R ^ 2 * (δ ^ 2 * (239 / 240)) := by ring
    _ ≤ R ^ 2 * (2 - 2 * c) := hmul
    _ ≤ D2 := hD

/-- Circles of one layer of a shell `k >= 4` are at least `0.78 L_k` apart,
hence at least `0.78 s_k`: the paper's same-layer spacing bound. -/
theorem lattice_same_layer_separated (k : ℕ) (hk : 4 ≤ k) (i : Fin (latticeLayerCount k))
    {j j' : Fin (latticeCirclesPerLayer k)} (hj : j ≠ j') {x y : LatticeSpace}
    (hx : x ∈ indexedLatticeCircle k i j) (hy : y ∈ indexedLatticeCircle k i j') :
    (78 / 100 : ℝ) * latticeLayerCount k ≤ dist x y := by
  have hLpos : (0 : ℝ) < latticeLayerCount k := by unfold latticeLayerCount; positivity
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hNval := latticeCircleCount_cast k
  have hLN := lattice_layer_count_le k hk
  have hRlo := (latticeCircleRadius_bounds k i).1
  have hR0 : 0 ≤ latticeCircleRadius k i := le_trans hp.le hRlo
  have hθb := latticePolarAngle_bounds k (latticeAngleIndex k (i, j))
  have hθb' := latticePolarAngle_bounds k (latticeAngleIndex k (i, j'))
  have hmain := latitudeCircle_dist_sq_ge hR0 hR0
    (Real.sin_nonneg_of_nonneg_of_le_pi hθb.1.le hθb.2.le)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθb'.1.le hθb'.2.le) hx hy
  have hgap := lattice_same_layer_angle_gap k i hj
  have hP3 : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hP4 : Real.pi < (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.pi * (latticeLayerCount k : ℝ) / (latticeCircleCount k : ℝ) :=
    ⟨_, rfl⟩
  rw [← hδ] at hgap
  obtain ⟨hδpos, hδsmall⟩ := same_layer_delta_small hLpos hp hNval hLN hP3 hP4 hδ
  have habs : |latticePolarAngle k (latticeAngleIndex k (i, j)) -
      latticePolarAngle k (latticeAngleIndex k (i, j'))| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hθb.1, hθb.2, hθb'.1, hθb'.2]
  have hcos1 : Real.cos (latticePolarAngle k (latticeAngleIndex k (i, j)) -
      latticePolarAngle k (latticeAngleIndex k (i, j'))) ≤ Real.cos δ := by
    rw [← Real.cos_abs (latticePolarAngle k (latticeAngleIndex k (i, j)) -
      latticePolarAngle k (latticeAngleIndex k (i, j')))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδpos.le habs hgap
  have hcos2 : Real.cos δ ≤ 1 - δ ^ 2 / 2 + δ ^ 4 * (5 / 96) := by
    have hb := Real.cos_bound (x := δ) (by rw [abs_of_pos hδpos]; linarith)
    rw [abs_of_pos hδpos] at hb
    linarith [(abs_le.mp hb).2]
  have hD : latticeCircleRadius k i ^ 2 *
      (2 - 2 * Real.cos (latticePolarAngle k (latticeAngleIndex k (i, j)) -
        latticePolarAngle k (latticeAngleIndex k (i, j')))) ≤ dist x y ^ 2 := by
    refine le_trans (le_of_eq ?_) hmain
    ring
  have hfinal := same_layer_arith hLpos hp hNval hLN hRlo hP3 hP4 hδ (hcos1.trans hcos2) hD
  exact (abs_le_of_sq_le_sq' hfinal dist_nonneg).2

/-- The dyadic radial mesh of shell `k` is at least `0.7 sqrt (2^k)`. -/
theorem lattice_mesh_ge_sqrt (k : ℕ) :
    (7 / 10 : ℝ) * Real.sqrt ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ k / latticeLayerCount k := by
  rw [lattice_radial_mesh]
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (k / 2) := by positivity
  have hsq : ((7 / 10 : ℝ) * Real.sqrt ((2 : ℝ) ^ k)) ^ 2 ≤ ((2 : ℝ) ^ (k / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    have hk : k ≤ k / 2 * 2 + 1 := by omega
    have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k / 2 * 2 + 1) :=
      pow_le_pow_right₀ (by norm_num) hk
    rw [pow_succ] at hp
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (k / 2 * 2) by positivity]
  exact (abs_le_of_sq_le_sq' hsq h0).2

/-- The layer count dominates `sqrt (2^k)`. -/
theorem lattice_layer_count_ge_sqrt (k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ k) ≤ latticeLayerCount k := by
  have hcast : (latticeLayerCount k : ℝ) = (2 : ℝ) ^ ((k + 1) / 2) := by
    simp [latticeLayerCount]
  rw [hcast]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Two distinct circles of one shell `k >= 4` are at least `0.7 s_k` apart,
with `s_k = sqrt (2^k)`. Distinct layers use the radial mesh, one layer uses
the angular spacing. -/
theorem lattice_same_shell_separated (k : ℕ) (hk : 4 ≤ k)
    {i i' : Fin (latticeLayerCount k)} {j j' : Fin (latticeCirclesPerLayer k)}
    (hne : (i, j) ≠ (i', j')) {x y : LatticeSpace}
    (hx : x ∈ indexedLatticeCircle k i j) (hy : y ∈ indexedLatticeCircle k i' j') :
    (7 / 10 : ℝ) * Real.sqrt ((2 : ℝ) ^ k) ≤ dist x y := by
  have hs0 : 0 ≤ Real.sqrt ((2 : ℝ) ^ k) := Real.sqrt_nonneg _
  rcases lt_trichotomy i.val i'.val with h | h | h
  · exact (lattice_mesh_ge_sqrt k).trans (lattice_distinct_layers_separated k h j j' hx hy)
  · have hi : i = i' := Fin.ext h
    subst hi
    have hj : j ≠ j' := fun hjj => hne (by rw [hjj])
    have h1 := lattice_same_layer_separated k hk i hj hx hy
    have h2 := lattice_layer_count_ge_sqrt k
    nlinarith
  · rw [dist_comm]
    exact (lattice_mesh_ge_sqrt k).trans (lattice_distinct_layers_separated k h j' j hy hx)

/-- Circles of two different shells `k < k'` are separated by the radial mesh
of the lower shell, hence by at least `0.7 s_k`. -/
theorem lattice_distinct_shells_separated {k k' : ℕ} (hkk : k < k')
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k))
    (i' : Fin (latticeLayerCount k')) (j' : Fin (latticeCirclesPerLayer k'))
    {x y : LatticeSpace} (hx : x ∈ indexedLatticeCircle k i j)
    (hy : y ∈ indexedLatticeCircle k' i' j') :
    (7 / 10 : ℝ) * Real.sqrt ((2 : ℝ) ^ k) ≤ dist x y := by
  refine (lattice_mesh_ge_sqrt k).trans ?_
  have hn := norm_sub_norm_le y x
  rw [← dist_eq_norm, dist_comm, hx.1, hy.1] at hn
  have hup := latticeCircleRadius_upper_gap k i
  have hlo := (latticeCircleRadius_bounds k' i').1
  have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) hkk
  linarith

/-- Every circle of a shell below `k + 1` stays inside the ball of radius
`2^(k+1)` minus the radial mesh of shell `k`: the inner clearance used in the
local comparison of `thm:B`(a). -/
theorem lattice_lower_shell_radius_le {k k' : ℕ} (hkk : k' ≤ k)
    (i : Fin (latticeLayerCount k')) :
    latticeCircleRadius k' i ≤ (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ (k' / 2) := by
  have hup := latticeCircleRadius_upper_gap k' i
  rw [lattice_radial_mesh] at hup
  have hp : (2 : ℝ) ^ (k' + 1) ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

end BrownRadial
