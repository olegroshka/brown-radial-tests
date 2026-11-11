import LatticeCovering
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-!
The covering used in the proof of `lem:circle`, scales `rho >= a / 6`: the
cubes of the grid of side `h` (centres in `h Z^3`) that meet the closed ball
`2B = closedBall x0 (2 rho)`. No weight and no measure occurs in this file.

For every `h > 0`:

* the index set `gridIndex h x0 rho` is finite and its cubes cover the closed
  ball `2B` (`grid_index_finite`, `grid_cover`);
* every point lies in at most `8` cubes of the grid (`grid_cube_overlap`);
* if the `1.01`-fold enlargements of two cubes meet, their integer indices
  differ by at most one in each coordinate (`grid_neighbor_index`): a cube
  has itself and at most `26` others as neighbours;
* the enlargement of a neighbour lies in the concentric cube of side
  `3.01 h` (`grid_neighbor_subset_cube`), hence in the ball about the centre
  of radius `0.163 * 16 h` (`grid_neighbor_subset_ball`); this is the paper's
  "radius at most `0.163 R`" with `h = R / 16`;
* if `h <= 0.57 rho`, in particular if `16 h <= 6 rho`, the ball
  `B_j = B(c_j, 0.163 * 16 h)` of every cube that meets the closed `2B` lies
  in `4B` (`grid_ball_subset`);
* every point lies in at most `216` of the balls `B_j` (`grid_ball_overlap`).

`grid_gluing_hypotheses` collects these in the form of the hypotheses of
`gluing_lemma`, with enlargement factor `101 / 100`, overlap bounds `8` and
`216`, side ratio `1` and radius ratio `326 / 125 = 0.163 * 16`.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-- The centre `h z` of the grid cube with integer index `z`. -/
noncomputable def gridCenter (h : ℝ) (z : Fin 3 → ℤ) : LatticeSpace :=
  WithLp.toLp 2 (fun i => h * (z i : ℝ))

theorem gridCenter_apply (h : ℝ) (z : Fin 3 → ℤ) (i : Fin 3) :
    gridCenter h z i = h * (z i : ℝ) := rfl

/-- The indices of the grid cubes of side `h` that meet the closed ball
`closedBall x0 (2 rho)`. -/
def gridIndex (h : ℝ) (x0 : LatticeSpace) (ρ : ℝ) : Set (Fin 3 → ℤ) :=
  {z | (cube (gridCenter h z) h ∩ closedBall x0 (2 * ρ)).Nonempty}

/-! ### Scalar facts -/

theorem grid_abs_eq {h : ℝ} (hh : 0 < h) (p z : ℝ) : |p - h * z| = h * |p / h - z| := by
  have e : p - h * z = h * (p / h - z) := by field_simp
  rw [e, abs_mul, abs_of_pos hh]

theorem grid_coord_le_dist (a b : LatticeSpace) (i : Fin 3) : |a i - b i| ≤ dist a b := by
  have h := PiLp.norm_apply_le (a - b) i
  rw [dist_eq_norm]
  simpa [Real.norm_eq_abs] using h

theorem grid_sqrt_three : Real.sqrt 3 ≤ 17321 / 10000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

/-- A point of the cube with index `z` and side `kappa h`, in units of `h`. -/
theorem grid_coord_of_mem_cube {h : ℝ} (hh : 0 < h) {z : Fin 3 → ℤ} {p : LatticeSpace} {κ : ℝ}
    (hp : p ∈ cube (gridCenter h z) (κ * h)) (i : Fin 3) : |p i / h - (z i : ℝ)| ≤ κ / 2 := by
  have h1 := hp i
  rw [gridCenter_apply, grid_abs_eq hh] at h1
  exact le_of_mul_le_mul_left (by linarith) hh

/-- A point of the open ball about the centre with index `z` and radius
`t h`, in units of `h`. -/
theorem grid_coord_of_mem_ball {h : ℝ} (hh : 0 < h) {z : Fin 3 → ℤ} {p : LatticeSpace} {t : ℝ}
    (hp : p ∈ ball (gridCenter h z) (t * h)) (i : Fin 3) : |p i / h - (z i : ℝ)| < t := by
  rw [mem_ball] at hp
  have h1 := grid_coord_le_dist p (gridCenter h z) i
  rw [gridCenter_apply, grid_abs_eq hh] at h1
  exact lt_of_mul_lt_mul_left (by linarith) hh.le

/-! ### Finiteness and covering -/

/-- Only finitely many grid cubes meet a closed ball. -/
theorem grid_index_finite {h : ℝ} (hh : 0 < h) (x0 : LatticeSpace) (ρ : ℝ) :
    (gridIndex h x0 ρ).Finite := by
  refine (Set.Finite.pi (fun i : Fin 3 =>
    Set.finite_Icc ⌊(x0 i - 2 * ρ) / h - 1 / 2⌋ ⌈(x0 i + 2 * ρ) / h + 1 / 2⌉)).subset ?_
  rintro z ⟨p, hp, hpb⟩
  rw [Set.mem_univ_pi]
  intro i
  rw [mem_closedBall] at hpb
  have h1 := grid_coord_of_mem_cube hh (κ := 1) (by rwa [one_mul]) i
  have h2 := grid_coord_le_dist p x0 i
  rw [abs_le] at h1 h2
  have e1 : (x0 i - 2 * ρ) / h = x0 i / h - 2 * ρ / h := by ring
  have e2 : (x0 i + 2 * ρ) / h = x0 i / h + 2 * ρ / h := by ring
  have h3 : p i / h - x0 i / h ≤ 2 * ρ / h := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  have h4 : -(2 * ρ / h) ≤ p i / h - x0 i / h := by
    rw [← sub_div, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  rw [Set.mem_Icc]
  constructor
  · have h5 := Int.floor_le ((x0 i - 2 * ρ) / h - 1 / 2)
    have h6 : ((⌊(x0 i - 2 * ρ) / h - 1 / 2⌋ : ℤ) : ℝ) ≤ (z i : ℝ) := by
      linarith [h1.1, h1.2, e1]
    exact_mod_cast h6
  · have h5 := Int.le_ceil ((x0 i + 2 * ρ) / h + 1 / 2)
    have h6 : (z i : ℝ) ≤ ((⌈(x0 i + 2 * ρ) / h + 1 / 2⌉ : ℤ) : ℝ) := by
      linarith [h1.1, h1.2, e2]
    exact_mod_cast h6

/-- The grid cubes that meet the closed ball `2B` cover it. -/
theorem grid_cover {h : ℝ} (hh : 0 < h) (x0 : LatticeSpace) (ρ : ℝ) :
    closedBall x0 (2 * ρ) ⊆ ⋃ z : gridIndex h x0 ρ, cube (gridCenter h z) h := by
  intro p hp
  have hmem : p ∈ cube (gridCenter h (fun i => round (p i / h))) h := by
    intro i
    rw [gridCenter_apply, grid_abs_eq hh]
    have h1 := abs_sub_round (p i / h)
    nlinarith
  exact mem_iUnion.mpr ⟨⟨_, p, hmem, hp⟩, hmem⟩

/-! ### Counting integer points in a window -/

/-- A set of integer triples whose coordinates lie in windows of `N`
consecutive integers has at most `N^3` elements. -/
theorem grid_card_le_of_window (T : Finset (Fin 3 → ℤ)) (lo : Fin 3 → ℤ) (N : ℕ)
    (hT : ∀ z ∈ T, ∀ i, lo i ≤ z i ∧ z i < lo i + N) : T.card ≤ N ^ 3 := by
  have hsub : T ⊆ Fintype.piFinset (fun i => Finset.Ico (lo i) (lo i + N)) := by
    intro z hz
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Ico]
    exact hT z hz i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp [Int.card_Ico]

/-- **Overlap of the cubes.** Every point lies in at most `8` cubes of the
grid. -/
theorem grid_cube_overlap {h : ℝ} (hh : 0 < h) (p : LatticeSpace) (T : Finset (Fin 3 → ℤ))
    (hT : ∀ z ∈ T, p ∈ cube (gridCenter h z) h) : T.card ≤ 8 := by
  have hw := grid_card_le_of_window T (fun i => ⌈p i / h - 1 / 2⌉) 2 ?_
  · norm_num at hw
    exact hw
  intro z hz i
  have h1 := grid_coord_of_mem_cube hh (κ := 1) (by rw [one_mul]; exact hT z hz) i
  rw [abs_le] at h1
  constructor
  · exact Int.ceil_le.mpr (by linarith)
  · have h3 := Int.le_ceil (p i / h - 1 / 2)
    have h4 : (z i : ℝ) < ((⌈p i / h - 1 / 2⌉ + ((2 : ℕ) : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4

/-- **Overlap of the balls.** Every point lies in at most `216` of the balls
of radius `0.163 * 16 h` about the centres of the grid. -/
theorem grid_ball_overlap {h : ℝ} (hh : 0 < h) (p : LatticeSpace) (T : Finset (Fin 3 → ℤ))
    (hT : ∀ z ∈ T, p ∈ ball (gridCenter h z) (163 / 1000 * (16 * h))) : T.card ≤ 216 := by
  have hw := grid_card_le_of_window T (fun i => ⌈p i / h - 326 / 125⌉) 6 ?_
  · norm_num at hw
    exact hw
  intro z hz i
  have h1 := grid_coord_of_mem_ball hh (t := 326 / 125)
    (by rw [show (326 / 125 : ℝ) * h = 163 / 1000 * (16 * h) by ring]; exact hT z hz) i
  rw [abs_lt] at h1
  constructor
  · exact Int.ceil_le.mpr (by linarith)
  · have h3 := Int.le_ceil (p i / h - 326 / 125)
    have h4 : (z i : ℝ) < ((⌈p i / h - 326 / 125⌉ + ((6 : ℕ) : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4

/-! ### Neighbours -/

/-- If the `1.01`-fold enlargements of two grid cubes meet, their indices
differ by at most one in each coordinate. So the neighbours of a cube are
itself and at most `26` others (paper: "its 26 neighbours"). -/
theorem grid_neighbor_index {h : ℝ} (hh : 0 < h) {z z' : Fin 3 → ℤ}
    (hn : (cube (gridCenter h z) (101 / 100 * h) ∩
      cube (gridCenter h z') (101 / 100 * h)).Nonempty) (i : Fin 3) : |z i - z' i| ≤ 1 := by
  obtain ⟨q, hq, hq'⟩ := hn
  have h1 := grid_coord_of_mem_cube hh hq i
  have h2 := grid_coord_of_mem_cube hh hq' i
  have h3 : |(z i : ℝ) - (z' i : ℝ)| < 1 + 1 := by
    rw [abs_le] at h1 h2
    rw [abs_lt]
    constructor <;> linarith
  have h4 : |z i - z' i| < 1 + 1 := by exact_mod_cast h3
  exact Int.lt_add_one_iff.mp h4

/-- Paper: the `1.01`-fold enlargements of a cube and of its neighbours lie
in the concentric cube of side `3.01 h`. -/
theorem grid_neighbor_subset_cube {h : ℝ} (hh : 0 < h) {z z' : Fin 3 → ℤ}
    (hn : (cube (gridCenter h z) (101 / 100 * h) ∩
      cube (gridCenter h z') (101 / 100 * h)).Nonempty) :
    cube (gridCenter h z) (101 / 100 * h) ⊆ cube (gridCenter h z') (301 / 100 * h) := by
  intro y hy i
  have h1 := hy i
  have h2 := grid_neighbor_index hh hn i
  have h3 : |(z i : ℝ) - (z' i : ℝ)| ≤ 1 := by exact_mod_cast h2
  rw [gridCenter_apply] at h1 ⊢
  have h4 : |h * (z i : ℝ) - h * (z' i : ℝ)| ≤ h := by
    rw [← mul_sub, abs_mul, abs_of_pos hh]
    nlinarith
  have h5 := abs_sub_le (y i) (h * (z i : ℝ)) (h * (z' i : ℝ))
  linarith

/-- Paper: "each ball `B_j` has radius at most `0.163 R`", `R = 16 h`. The
enlargement of every neighbour of a cube lies in the open ball about the
centre of that cube of radius `0.163 * 16 h`; the half-diagonal of the cube
of side `3.01 h` is `sqrt 3 * 3.01 h / 2 < 2.6069 h < 2.608 h`. -/
theorem grid_neighbor_subset_ball {h : ℝ} (hh : 0 < h) {z z' : Fin 3 → ℤ}
    (hn : (cube (gridCenter h z) (101 / 100 * h) ∩
      cube (gridCenter h z') (101 / 100 * h)).Nonempty) :
    cube (gridCenter h z) (101 / 100 * h) ⊆ ball (gridCenter h z') (163 / 1000 * (16 * h)) := by
  refine (grid_neighbor_subset_cube hh hn).trans ?_
  intro y hy
  have h1 := cube_subset_closedBall _ _ hy
  rw [mem_closedBall] at h1
  rw [mem_ball]
  have h3 : Real.sqrt ((3 : ℕ) : ℝ) ≤ 17321 / 10000 := by
    rw [Nat.cast_ofNat]
    exact grid_sqrt_three
  have h4 := mul_le_mul_of_nonneg_right h3 hh.le
  linarith

/-! ### Position of the balls -/

/-- **`B_j` inside `4B`.** If `h <= 0.57 rho`, the ball of radius
`0.163 * 16 h` about the centre of a grid cube that meets the closed ball
`2B` lies in the open ball `4B`. The paper does not verify this hypothesis of
`lem:glue`; it holds for `h = a / 16` and every `rho >= a / 6`, where
`h <= 0.375 rho`. -/
theorem grid_ball_subset {h : ℝ} (hh : 0 < h) {x0 : LatticeSpace} {ρ : ℝ}
    (hsmall : 100 * h ≤ 57 * ρ) {z : Fin 3 → ℤ} (hz : z ∈ gridIndex h x0 ρ) :
    ball (gridCenter h z) (163 / 1000 * (16 * h)) ⊆ ball x0 (4 * ρ) := by
  obtain ⟨p, hp, hpb⟩ := hz
  have d1 := cube_subset_closedBall _ _ hp
  rw [mem_closedBall] at d1 hpb
  have h3 : Real.sqrt ((3 : ℕ) : ℝ) ≤ 17321 / 10000 := by
    rw [Nat.cast_ofNat]
    exact grid_sqrt_three
  have h4 := mul_le_mul_of_nonneg_right h3 hh.le
  have tri := dist_triangle (gridCenter h z) p x0
  rw [dist_comm (gridCenter h z) p] at tri
  apply ball_subset_ball'
  linarith

/-- Paper: "cubes of side `R / 16`, of diameter `sqrt 3 R / 16 < rho`", for
`rho >= R / 6`. Here: `16 h <= 6 rho` gives `sqrt 3 * h <= rho`. -/
theorem grid_diam_le {h ρ : ℝ} (hh : 0 < h) (hsmall : 16 * h ≤ 6 * ρ) :
    Real.sqrt 3 * h ≤ ρ := by
  have h4 := mul_le_mul_of_nonneg_right grid_sqrt_three hh.le
  linarith

/-! ### The hypotheses of the gluing lemma -/

/-- **The grid in the form the gluing lemma asks for.** For `h > 0` and a
ball `B = B(x_0, rho)` with `16 h <= 6 rho`, the family of the grid cubes of
side `h` that meet the closed ball `2B`, with the balls
`B_z = B(h z, 0.163 * 16 h)`, satisfies every geometric hypothesis of
`gluing_lemma` in dimension three with enlargement factor `1.01`, overlap
bounds `8` and `216`, side ratio `1` and radius ratio `326 / 125`. -/
theorem grid_gluing_hypotheses {h : ℝ} (hh : 0 < h) (x0 : LatticeSpace) {ρ : ℝ}
    (hsmall : 16 * h ≤ 6 * ρ) :
    (gridIndex h x0 ρ).Finite ∧
    closedBall x0 (2 * ρ) ⊆ ⋃ z : gridIndex h x0 ρ, cube (gridCenter h z) h ∧
    (∀ x, ∀ T : Finset (gridIndex h x0 ρ),
      (∀ z ∈ T, x ∈ cube (gridCenter h z) h) → T.card ≤ 8) ∧
    (∀ _z : gridIndex h x0 ρ, Real.sqrt ((3 : ℕ) : ℝ) * h ≤ ρ) ∧
    (∀ i j : gridIndex h x0 ρ,
      cubeNeighbor (101 / 100) (fun z : gridIndex h x0 ρ => gridCenter h z) (fun _ => h) i j →
        h ≤ 1 * h) ∧
    (∀ i j : gridIndex h x0 ρ,
      cubeNeighbor (101 / 100) (fun z : gridIndex h x0 ρ => gridCenter h z) (fun _ => h) i j →
        cube (gridCenter h i) (101 / 100 * h) ⊆ ball (gridCenter h j) (163 / 1000 * (16 * h))) ∧
    (∀ _z : gridIndex h x0 ρ, 163 / 1000 * (16 * h) ≤ 326 / 125 * h) ∧
    (∀ z : gridIndex h x0 ρ, ball (gridCenter h z) (163 / 1000 * (16 * h)) ⊆ ball x0 (4 * ρ)) ∧
    (∀ x, ∀ T : Finset (gridIndex h x0 ρ),
      (∀ z ∈ T, x ∈ ball (gridCenter h z) (163 / 1000 * (16 * h))) → T.card ≤ 216) := by
  have hρ : 0 < ρ := by linarith
  refine ⟨grid_index_finite hh x0 ρ, grid_cover hh x0 ρ, ?_, ?_, fun _ _ _ => by rw [one_mul],
    fun i j hij => grid_neighbor_subset_ball hh hij, fun _ => le_of_eq (by ring),
    fun z => grid_ball_subset hh (by linarith) z.2, ?_⟩
  · intro x T hT
    have h1 := grid_cube_overlap hh x (T.map (Function.Embedding.subtype _)) ?_
    · rwa [Finset.card_map] at h1
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
    exact hT a ha
  · intro _
    rw [Nat.cast_ofNat]
    exact grid_diam_le hh hsmall
  · intro x T hT
    have h1 := grid_ball_overlap hh x (T.map (Function.Embedding.subtype _)) ?_
    · rwa [Finset.card_map] at h1
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
    exact hT a ha

end BrownRadial
