import LatticeRegularity
import GaussianSmooth
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.LocallyFinite

open Set Metric
open scoped NNReal ENNReal BigOperators ContDiff
namespace BrownRadial

abbrev LatticeSpace := EuclideanSpace ℝ (Fin 3)

def latticeCircleCount (k : ℕ) : ℕ := 2^(k+2)
def latticeLayerCount (k : ℕ) : ℕ := 2^((k+1)/2)
def latticeCirclesPerLayer (k : ℕ) : ℕ := 2^(k+2-(k+1)/2)

theorem lattice_counts_product (k : ℕ) :
    latticeCirclesPerLayer k * latticeLayerCount k = latticeCircleCount k := by
  unfold latticeCirclesPerLayer latticeLayerCount latticeCircleCount
  rw [← pow_add]
  congr 1
  omega

/-- The paper's row-major index n = j L_k + i, as an actual bijection. -/
def latticeAngleIndex (k : ℕ) :
    Fin (latticeLayerCount k) × Fin (latticeCirclesPerLayer k) ≃ Fin (latticeCircleCount k) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (lattice_counts_product k)))

theorem latticeAngleIndex_val (k : ℕ)
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k)) :
    (latticeAngleIndex k (i,j)).val = j.val * latticeLayerCount k + i.val := by
  simp [latticeAngleIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

noncomputable def latticePolarAngle (k : ℕ) (n : Fin (latticeCircleCount k)) : ℝ :=
  Real.pi * ((n.val : ℝ)+1/2) / latticeCircleCount k

noncomputable def latticeCircleRadius (k : ℕ) (i : Fin (latticeLayerCount k)) : ℝ :=
  (2:ℝ)^k + i.val * ((2:ℝ)^k / latticeLayerCount k)

/-- A latitude circle in Euclidean three-space. The polar-angle constraint is
expressed as its third-coordinate height, avoiding a choice of azimuth. -/
def latitudeCircle (R θ : ℝ) : Set LatticeSpace :=
  {x | ‖x‖ = R ∧ x 2 = R * Real.cos θ}

noncomputable def latitudePoint (R θ φ : ℝ) : LatticeSpace :=
  WithLp.toLp 2 ![R*Real.sin θ*Real.cos φ, R*Real.sin θ*Real.sin φ, R*Real.cos θ]

theorem latitudePoint_norm_sq (R θ φ : ℝ) : ‖latitudePoint R θ φ‖^2 = R^2 := by
  calc
    _ = R^2*((Real.sin θ)^2*((Real.sin φ)^2+(Real.cos φ)^2)+(Real.cos θ)^2) := by
      simp only [latitudePoint, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three,
        WithLp.toLp, id_eq, Real.norm_eq_abs, sq_abs]
      change (R*Real.sin θ*Real.cos φ)^2 + (R*Real.sin θ*Real.sin φ)^2 + (R*Real.cos θ)^2 = _
      ring
    _ = R^2 := by rw [Real.sin_sq_add_cos_sq, mul_one, Real.sin_sq_add_cos_sq, mul_one]

theorem latitudePoint_mem {R : ℝ} (hR : 0 ≤ R) (θ φ : ℝ) :
    latitudePoint R θ φ ∈ latitudeCircle R θ := by
  constructor
  · exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (latitudePoint_norm_sq R θ φ)
  · simp [latitudePoint]

theorem latitudeCircle_nonempty {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    (latitudeCircle R θ).Nonempty := ⟨latitudePoint R θ 0, latitudePoint_mem hR θ 0⟩

theorem latitudeCircle_isClosed (R θ : ℝ) : IsClosed (latitudeCircle R θ) :=
  (isClosed_eq continuous_norm continuous_const).inter
    (isClosed_eq (EuclideanSpace.proj (2 : Fin 3)).continuous continuous_const)

theorem latitudeCircle_isCompact (R θ : ℝ) : IsCompact (latitudeCircle R θ) := by
  apply (isCompact_closedBall (0 : LatticeSpace) R).of_isClosed_subset (latitudeCircle_isClosed R θ)
  intro x hx
  simpa only [mem_closedBall, dist_zero_right, hx.1] using le_rfl (a := R)

theorem latticeCircleRadius_bounds (k : ℕ) (i : Fin (latticeLayerCount k)) :
    (2:ℝ)^k ≤ latticeCircleRadius k i ∧ latticeCircleRadius k i < (2:ℝ)^(k+1) := by
  have hL : (0:ℝ) < latticeLayerCount k := by unfold latticeLayerCount; positivity
  have hi : (i.val : ℝ) < latticeLayerCount k := by exact_mod_cast i.isLt
  have hr : 0 < (2:ℝ)^k := by positivity
  unfold latticeCircleRadius
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (div_pos hr hL).le)
  · have h := mul_lt_mul_of_pos_right hi (div_pos hr hL)
    have he : (latticeLayerCount k : ℝ) * ((2:ℝ)^k / latticeLayerCount k) = (2:ℝ)^k := by field_simp
    rw [he] at h
    rw [pow_succ]
    linarith

/-- The outermost layer stays one complete radial mesh step below the next
dyadic shell. This supplies a quantitative gap, not merely disjoint shells. -/
theorem latticeCircleRadius_upper_gap (k : ℕ) (i : Fin (latticeLayerCount k)) :
    latticeCircleRadius k i ≤ (2:ℝ)^(k+1) - (2:ℝ)^k/latticeLayerCount k := by
  have hL : (0:ℝ) < latticeLayerCount k := by unfold latticeLayerCount; positivity
  have hi : (i.val:ℝ)+1 ≤ latticeLayerCount k := by exact_mod_cast i.isLt
  have h := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ (2:ℝ)^k/latticeLayerCount k)
  have he : (latticeLayerCount k:ℝ) * ((2:ℝ)^k/latticeLayerCount k) = (2:ℝ)^k := by field_simp
  rw [he] at h
  unfold latticeCircleRadius
  rw [pow_succ]
  nlinarith

/-- The exact radial mesh is a dyadic integer; this is the parity-dependent
spacing described in the construction. -/
theorem lattice_radial_mesh (k : ℕ) :
    (2:ℝ)^k/latticeLayerCount k = (2:ℝ)^(k/2) := by
  have hk : k = k/2 + (k+1)/2 := by omega
  have hcast : (latticeLayerCount k:ℝ) = (2:ℝ)^((k+1)/2) := by simp [latticeLayerCount]
  rw [hcast]
  conv_lhs => rw [hk, pow_add]
  field_simp
  congr 1
  omega

theorem latticePolarAngle_bounds (k : ℕ) (n : Fin (latticeCircleCount k)) :
    0 < latticePolarAngle k n ∧ latticePolarAngle k n < Real.pi := by
  have hN : (0:ℝ) < latticeCircleCount k := by unfold latticeCircleCount; positivity
  have hn : (n.val : ℝ)+1 ≤ latticeCircleCount k := by exact_mod_cast n.isLt
  unfold latticePolarAngle
  constructor
  · positivity
  · apply (div_lt_iff₀ hN).mpr
    nlinarith [Real.pi_pos]

noncomputable def indexedLatticeCircle (k : ℕ)
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k)) : Set LatticeSpace :=
  latitudeCircle (latticeCircleRadius k i) (latticePolarAngle k (latticeAngleIndex k (i,j)))

/-- The actual union in the paper, starting at shell k = 4. -/
def latticeValleys : Set LatticeSpace :=
  ⋃ k : {k : ℕ // 4 ≤ k}, ⋃ i : Fin (latticeLayerCount k.val),
    ⋃ j : Fin (latticeCirclesPerLayer k.val), indexedLatticeCircle k.val i j

theorem indexedLatticeCircle_in_shell (k : ℕ)
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k)) :
    indexedLatticeCircle k i j ⊆ {x | (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(k+1)} := by
  intro x hx
  change (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(k+1)
  rw [show ‖x‖ = latticeCircleRadius k i from hx.1]
  exact latticeCircleRadius_bounds k i

/-- Points on different radial layers of one shell are separated by at least
one mesh step, regardless of their azimuth or polar angles. -/
theorem lattice_distinct_layers_separated (k : ℕ)
    {i i' : Fin (latticeLayerCount k)} (hi : i.val < i'.val)
    (j : Fin (latticeCirclesPerLayer k)) (j' : Fin (latticeCirclesPerLayer k))
    {x y : LatticeSpace} (hx : x ∈ indexedLatticeCircle k i j)
    (hy : y ∈ indexedLatticeCircle k i' j') :
    (2:ℝ)^k/latticeLayerCount k ≤ dist x y := by
  have hL : (0:ℝ) < latticeLayerCount k := by unfold latticeLayerCount; positivity
  have hi' : (i.val:ℝ)+1 ≤ i'.val := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_right hi' (by positivity : 0 ≤ (2:ℝ)^k/latticeLayerCount k)
  have hn := norm_sub_norm_le y x
  rw [← dist_eq_norm, dist_comm, hx.1, hy.1] at hn
  dsimp [latticeCircleRadius] at hn
  nlinarith

/-- Consecutive shells retain the previous shell's entire radial mesh gap. -/
theorem lattice_consecutive_shells_separated (k : ℕ)
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k))
    (i' : Fin (latticeLayerCount (k+1))) (j' : Fin (latticeCirclesPerLayer (k+1)))
    {x y : LatticeSpace} (hx : x ∈ indexedLatticeCircle k i j)
    (hy : y ∈ indexedLatticeCircle (k+1) i' j') :
    (2:ℝ)^k/latticeLayerCount k ≤ dist x y := by
  have hn := norm_sub_norm_le y x
  rw [← dist_eq_norm, dist_comm, hx.1, hy.1] at hn
  linarith [(latticeCircleRadius_bounds (k+1) i').1, latticeCircleRadius_upper_gap k i]

theorem latticeValleys_nonempty : latticeValleys.Nonempty := by
  let i : Fin (latticeLayerCount 4) := ⟨0, by norm_num [latticeLayerCount]⟩
  let j : Fin (latticeCirclesPerLayer 4) := ⟨0, by norm_num [latticeCirclesPerLayer]⟩
  obtain ⟨x, hx⟩ := latitudeCircle_nonempty
    (le_trans (by positivity) (latticeCircleRadius_bounds 4 i).1)
    (latticePolarAngle 4 (latticeAngleIndex 4 (i,j)))
  refine ⟨x, ?_⟩
  exact mem_iUnion.mpr ⟨⟨4, le_rfl⟩, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hx⟩⟩⟩

/-- Only finitely many lattice shells meet any bounded neighborhood. -/
theorem lattice_shells_locallyFinite : LocallyFinite
    (fun k : ℕ => ⋃ i : Fin (latticeLayerCount k),
      ⋃ j : Fin (latticeCirclesPerLayer k), indexedLatticeCircle k i j) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖+1)
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, (Set.finite_Iio N).subset ?_⟩
  rintro k ⟨y, hy, hball⟩
  obtain ⟨i, hy⟩ := mem_iUnion.mp hy
  obtain ⟨j, hy⟩ := mem_iUnion.mp hy
  have hk : (k:ℝ) < (2:ℝ)^k := by exact_mod_cast (Nat.lt_two_pow_self (n := k))
  have hylo := (indexedLatticeCircle_in_shell k i j hy).1
  have hyhi : ‖y‖ < ‖x‖+1 := by
    have h := norm_sub_norm_le y x
    rw [mem_ball, dist_eq_norm] at hball
    linarith
  have hkN : (k:ℝ) < N := by linarith
  exact_mod_cast hkN

/-- The infinite valley union is closed: its shells escape every compact
region, while every individual shell is a finite union of compact circles. -/
theorem latticeValleys_isClosed : IsClosed latticeValleys := by
  apply (lattice_shells_locallyFinite.comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : {k : ℕ // 4 ≤ k} → ℕ))).isClosed_iUnion
  intro k
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  exact latitudeCircle_isClosed _ _

/-- A closest point in the actual infinite lattice exists, supplying the
nearest-circle existence premise used in the paper's local comparisons. -/
theorem lattice_nearest_point (x : LatticeSpace) :
    ∃ k : {k : ℕ // 4 ≤ k}, ∃ i : Fin (latticeLayerCount k.val),
      ∃ j : Fin (latticeCirclesPerLayer k.val), ∃ y ∈ indexedLatticeCircle k.val i j,
        infDist x latticeValleys = dist x y := by
  obtain ⟨y, hy, he⟩ := latticeValleys_isClosed.exists_infDist_eq_dist latticeValleys_nonempty x
  obtain ⟨k, hy⟩ := mem_iUnion.mp hy
  obtain ⟨i, hy⟩ := mem_iUnion.mp hy
  obtain ⟨j, hy⟩ := mem_iUnion.mp hy
  exact ⟨k, i, j, y, hy, he⟩

theorem lattice_nearest_circle (x : LatticeSpace) :
    ∃ k : {k : ℕ // 4 ≤ k}, ∃ i : Fin (latticeLayerCount k.val),
      ∃ j : Fin (latticeCirclesPerLayer k.val),
        infDist x (indexedLatticeCircle k.val i j) = infDist x latticeValleys := by
  obtain ⟨k,i,j,y,hy,he⟩ := lattice_nearest_point x
  refine ⟨k,i,j, le_antisymm ?_ ?_⟩
  · rw [he]
    exact infDist_le_dist_of_mem hy
  · apply infDist_le_infDist_of_subset _ ⟨y,hy⟩
    intro z hz
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j,hz⟩⟩⟩

/-- The far-case distance comparison used in the local proof, now with the
actual nearest lattice circle and actual distances throughout the ball. -/
theorem lattice_nearest_circle_far_comparison (x : LatticeSpace) {ρ : ℝ}
    (hfar : 2*ρ ≤ infDist x latticeValleys) :
    ∃ k : {k : ℕ // 4 ≤ k}, ∃ i : Fin (latticeLayerCount k.val),
      ∃ j : Fin (latticeCirclesPerLayer k.val),
        infDist x (indexedLatticeCircle k.val i j) = infDist x latticeValleys ∧
        ∀ y ∈ ball x ρ,
          infDist y latticeValleys ≤ infDist y (indexedLatticeCircle k.val i j) ∧
          infDist y (indexedLatticeCircle k.val i j) ≤ 3 * infDist y latticeValleys := by
  obtain ⟨k,i,j,he⟩ := lattice_nearest_circle x
  refine ⟨k,i,j,he, ?_⟩
  intro y hy
  have hne : (indexedLatticeCircle k.val i j).Nonempty :=
    latitudeCircle_nonempty (le_trans (by positivity) (latticeCircleRadius_bounds k.val i).1) _
  have hsub : indexedLatticeCircle k.val i j ⊆ latticeValleys := by
    intro z hz
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j,hz⟩⟩⟩
  refine ⟨infDist_le_infDist_of_subset hsub hne, ?_⟩
  have hlo : infDist x latticeValleys ≤ infDist y latticeValleys + dist x y :=
    infDist_le_infDist_add_dist
  have hhi : infDist y (indexedLatticeCircle k.val i j) ≤
      infDist x (indexedLatticeCircle k.val i j) + dist y x := infDist_le_infDist_add_dist
  rw [he] at hhi
  rw [mem_ball] at hy
  rw [dist_comm x y] at hlo
  exact far_distance_comparison hfar (by linarith) (by linarith)

/-- Midpoints of N equal cells cover the whole closed parameter interval,
including its right endpoint. -/
theorem midpoint_grid_cover {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (htN : t ≤ N) :
    ∃ n : Fin N, |t - ((n.val : ℝ)+1/2)| ≤ 1/2 := by
  by_cases he : t = (N : ℝ)
  · refine ⟨⟨N-1, by omega⟩, ?_⟩
    have hcast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [he, hcast]
    rw [show (N:ℝ)-((N:ℝ)-1+1/2) = 1/2 by ring]
    norm_num
  · have hn : ⌊t⌋₊ < N := (Nat.floor_lt ht).mpr (lt_of_le_of_ne htN he)
    refine ⟨⟨⌊t⌋₊, hn⟩, abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith [Nat.floor_le ht]
    · linarith [Nat.lt_floor_add_one t]

/-- Every polar direction is within the paper's pi/(2N_k) angular error of
an actual indexed circle; the row/column pair is recovered by the bijection. -/
theorem lattice_polar_coverage (k : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∃ i : Fin (latticeLayerCount k), ∃ j : Fin (latticeCirclesPerLayer k),
      |θ - latticePolarAngle k (latticeAngleIndex k (i,j))| ≤
        Real.pi / (2 * latticeCircleCount k) := by
  have hN : 0 < latticeCircleCount k := by unfold latticeCircleCount; positivity
  have hNr : (0:ℝ) < latticeCircleCount k := by exact_mod_cast hN
  let t : ℝ := latticeCircleCount k * θ / Real.pi
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htN : t ≤ latticeCircleCount k := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    exact mul_le_mul_of_nonneg_left hθπ hNr.le
  obtain ⟨n, hn⟩ := midpoint_grid_cover hN ht htN
  obtain ⟨⟨i,j⟩, hij⟩ := (latticeAngleIndex k).surjective n
  refine ⟨i, j, ?_⟩
  rw [hij]
  have he : θ - latticePolarAngle k n =
      (Real.pi / latticeCircleCount k) * (t - ((n.val : ℝ)+1/2)) := by
    dsimp [t, latticePolarAngle]
    field_simp [hNr.ne', Real.pi_ne_zero]
  rw [he, abs_mul, abs_of_pos (div_pos Real.pi_pos hNr)]
  calc
    _ ≤ (Real.pi / latticeCircleCount k) * (1/2) :=
      mul_le_mul_of_nonneg_left hn (div_pos Real.pi_pos hNr).le
    _ = Real.pi / (2 * latticeCircleCount k) := by ring

/-- The actual constructed lattice prior now has a smooth positive Gaussian
marginal with drift bounded by alpha/2. This does not assert its D+P or ray
properties, which require further geometric estimates. -/
theorem lattice_marginal_regular (α : ℝ≥0) :
    ContDiff ℝ ∞ (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys α)) ∧
    ∀ x : LatticeSpace,
      0 < gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys α) x ∧
      ‖gradient (fun y => Real.log
        (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys α) y)) x‖ ≤ (α:ℝ)/2 := by
  have hp := latticeWeight_pos latticeValleys (α:ℝ)
  have hl := latticeWeight_log_lipschitz latticeValleys α
  refine ⟨standardGaussianAverage_contDiff hp hl, fun x => ⟨gaussianAverage_pos _ hp hl x, ?_⟩⟩
  exact (standardGaussianAverage_bounded_drift hp hl x).2

end BrownRadial
