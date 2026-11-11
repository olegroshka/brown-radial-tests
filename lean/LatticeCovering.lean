import CubePartition
import LatticeGeometry
import Mathlib.MeasureTheory.Covering.Vitali

/-!
The covering used in the proof of `thm:B`(a), paragraph "Large balls": for
every ball `B = B(x_0, rho)`, a finite family of cubes `Q_j` with centres
`y_j` in the closed ball `2B` and sides `l_j = sigma(y_j) / 32`,
`sigma(y)^2 = 1 + |y|`, that covers the closed ball `2B` with bounded overlap,
together with the balls `B_j = B(y_j, 2.7 l_j)`.

The paper states the properties of such a covering and does not construct
it. Here it is constructed: Mathlib's Vitali selection gives a subfamily of
centres in `2B` whose cubes of side `sigma / 96` are pairwise disjoint and
whose cubes of side `sigma / 32` cover `2B`. Finiteness and the two overlap
bounds follow from the disjointness by the volume count of `CubePartition`.

The numbers of the paragraph are proved for every such family, with the
paper's enlargement factor `1.01`:

* `sigma` is `1/2`-Lipschitz (`lattice_covering_sigma_lipschitz`);
* neighbouring cubes have sides within a factor `1.03`
  (`lattice_covering_neighbor_sides`);
* the ball `B(y_j, 2.7 l_j)` contains the enlarged cubes of the neighbours
  of `j` (`lattice_covering_neighbor_subset_ball`), and `2.7 l_j` is less
  than `sigma(y_j) / 10` (`lattice_covering_ball_radius_lt`);
* if `sigma(x_0) <= 10 rho` and `Q_j` meets the closed ball `2B`, then
  `l_j <= 0.35 rho` (`lattice_covering_side_le`), `diam Q_j < rho`
  (`lattice_covering_diam_lt`) and `B_j` lies in `4B`
  (`lattice_covering_ball_subset`).

No weight and no measure of a weighted set occurs in this file.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### The scale `sigma` -/

/-- `sigma >= 1`. -/
theorem lattice_covering_sigma_one_le (y : LatticeSpace) : 1 ≤ Real.sqrt (1 + ‖y‖) := by
  rw [Real.one_le_sqrt]
  linarith [norm_nonneg y]

/-- Paper: `|grad sigma| <= 1/2`, as a Lipschitz bound. -/
theorem lattice_covering_sigma_lipschitz (x y : LatticeSpace) :
    Real.sqrt (1 + ‖x‖) ≤ Real.sqrt (1 + ‖y‖) + dist x y / 2 := by
  have hx := lattice_covering_sigma_one_le x
  have hy := lattice_covering_sigma_one_le y
  have hsx := Real.sq_sqrt (show (0:ℝ) ≤ 1 + ‖x‖ by positivity)
  have hsy := Real.sq_sqrt (show (0:ℝ) ≤ 1 + ‖y‖ by positivity)
  have hn : ‖x‖ - ‖y‖ ≤ dist x y := by
    rw [dist_eq_norm]
    exact norm_sub_norm_le x y
  by_contra h
  push_neg at h
  have hd : 0 ≤ dist x y := dist_nonneg
  have h1 : 0 ≤ (Real.sqrt (1 + ‖x‖) - Real.sqrt (1 + ‖y‖)) *
      (Real.sqrt (1 + ‖x‖) + Real.sqrt (1 + ‖y‖) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem lattice_covering_sqrt_three : Real.sqrt 3 ≤ 1733 / 1000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

/-- A point of a cube of side `s` in three-space is within `0.8665 s` of the
centre (half the diameter `sqrt 3 * s`). -/
theorem lattice_covering_cube_dist {c x : LatticeSpace} {s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ cube c s) : dist x c ≤ 1733 / 2000 * s := by
  have h := cube_subset_closedBall c s hx
  rw [mem_closedBall] at h
  have h3 : Real.sqrt ((3 : ℕ) : ℝ) ≤ 1733 / 1000 := by
    rw [Nat.cast_ofNat]
    exact lattice_covering_sqrt_three
  have h4 := mul_le_mul_of_nonneg_right h3 hs
  linarith

/-- Two cubes with sides at most `t * sigma(centre)` that meet: comparison of
`sigma` at the two centres. -/
theorem lattice_covering_sigma_of_meet {y z : LatticeSpace} {a b t : ℝ} (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (ha : a ≤ t * Real.sqrt (1 + ‖y‖)) (hb : b ≤ t * Real.sqrt (1 + ‖z‖))
    (h : (cube y a ∩ cube z b).Nonempty) :
    Real.sqrt (1 + ‖y‖) ≤ Real.sqrt (1 + ‖z‖) +
      1733 / 4000 * (t * Real.sqrt (1 + ‖y‖) + t * Real.sqrt (1 + ‖z‖)) := by
  obtain ⟨p, hp1, hp2⟩ := h
  have d1 := lattice_covering_cube_dist ha0 hp1
  have d2 := lattice_covering_cube_dist hb0 hp2
  have tri := dist_triangle y p z
  rw [dist_comm y p] at tri
  have lip := lattice_covering_sigma_lipschitz y z
  linarith

/-! ### The numbers of the paragraph "Large balls" -/

/-- Paper: cubes with `j' ~ j` (the `1.01`-fold enlargements meet) have sides
within a factor `1.03` of each other. -/
theorem lattice_covering_neighbor_sides {y z : LatticeSpace}
    (h : (cube y (101 / 100 * (Real.sqrt (1 + ‖y‖) / 32)) ∩
      cube z (101 / 100 * (Real.sqrt (1 + ‖z‖) / 32))).Nonempty) :
    Real.sqrt (1 + ‖y‖) / 32 ≤ 103 / 100 * (Real.sqrt (1 + ‖z‖) / 32) := by
  have hy := lattice_covering_sigma_one_le y
  have hz := lattice_covering_sigma_one_le z
  have h1 := lattice_covering_sigma_of_meet (t := 101 / 3200) (by positivity) (by positivity)
    (by linarith) (by linarith) h
  linarith

/-- Paper: the ball about `y_j` of radius `2.7 l_j` contains the enlarged
cube of every neighbour of `j`. -/
theorem lattice_covering_neighbor_subset_ball {y z : LatticeSpace}
    (h : (cube y (101 / 100 * (Real.sqrt (1 + ‖y‖) / 32)) ∩
      cube z (101 / 100 * (Real.sqrt (1 + ‖z‖) / 32))).Nonempty) :
    cube y (101 / 100 * (Real.sqrt (1 + ‖y‖) / 32)) ⊆
      ball z (27 / 10 * (Real.sqrt (1 + ‖z‖) / 32)) := by
  have hy := lattice_covering_sigma_one_le y
  have hz := lattice_covering_sigma_one_le z
  have hr := lattice_covering_neighbor_sides h
  obtain ⟨p, hp1, hp2⟩ := h
  intro x hx
  have hxz : x ∈ cube z (2 * (101 / 100 * (Real.sqrt (1 + ‖y‖) / 32)) +
      101 / 100 * (Real.sqrt (1 + ‖z‖) / 32)) := by
    intro i
    have a1 := hx i
    have a2 := hp1 i
    have a3 := hp2 i
    rw [abs_le] at a1 a2 a3 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have hd := lattice_covering_cube_dist (by positivity) hxz
  rw [mem_ball]
  linarith

/-- Paper: `2.7 l_j < sigma(y_j) / 10`, so `B_j` is a small ball. -/
theorem lattice_covering_ball_radius_lt (y : LatticeSpace) :
    27 / 10 * (Real.sqrt (1 + ‖y‖) / 32) < Real.sqrt (1 + ‖y‖) / 10 := by
  have hy := lattice_covering_sigma_one_le y
  linarith

/-- (G2) in the form of `lem:glue`, "doubling at scales at most `C s_j` around
`B_j`": every ball centred in `B_j` with radius at most that of `B_j` is a
small ball, radius at most `sigma / 10` at its own centre. -/
theorem lattice_covering_ball_inner_small {y a : LatticeSpace} {r : ℝ}
    (ha : a ∈ ball y (27 / 10 * (Real.sqrt (1 + ‖y‖) / 32)))
    (hr : r ≤ 27 / 10 * (Real.sqrt (1 + ‖y‖) / 32)) : r ≤ Real.sqrt (1 + ‖a‖) / 10 := by
  have hy := lattice_covering_sigma_one_le y
  rw [mem_ball] at ha
  have lip := lattice_covering_sigma_lipschitz y a
  rw [dist_comm y a] at lip
  linarith

/-- Paper: `l_j <= 0.35 rho` because `sigma_0 <= 10 rho`. For every cube of
side `sigma(y) / 32` centred at `y` that meets the closed ball `2B`; the
centre need not lie in `2B`. -/
theorem lattice_covering_side_le {x0 y : LatticeSpace} {ρ : ℝ}
    (hρ : Real.sqrt (1 + ‖x0‖) / 10 ≤ ρ)
    (h : (cube y (Real.sqrt (1 + ‖y‖) / 32) ∩ closedBall x0 (2 * ρ)).Nonempty) :
    Real.sqrt (1 + ‖y‖) / 32 ≤ 35 / 100 * ρ := by
  have hy := lattice_covering_sigma_one_le y
  have h0 := lattice_covering_sigma_one_le x0
  obtain ⟨p, hp1, hp2⟩ := h
  have d1 := lattice_covering_cube_dist (by positivity) hp1
  rw [mem_closedBall] at hp2
  have tri := dist_triangle y p x0
  rw [dist_comm y p] at tri
  have lip := lattice_covering_sigma_lipschitz y x0
  linarith

/-- Paper: `diam Q_j < rho`. -/
theorem lattice_covering_diam_lt {x0 y : LatticeSpace} {ρ : ℝ}
    (hρ : Real.sqrt (1 + ‖x0‖) / 10 ≤ ρ)
    (h : (cube y (Real.sqrt (1 + ‖y‖) / 32) ∩ closedBall x0 (2 * ρ)).Nonempty) :
    Real.sqrt 3 * (Real.sqrt (1 + ‖y‖) / 32) < ρ := by
  have hy := lattice_covering_sigma_one_le y
  have h0 := lattice_covering_sigma_one_le x0
  have hl := lattice_covering_side_le hρ h
  have h3 := mul_le_mul_of_nonneg_right lattice_covering_sqrt_three
    (show (0:ℝ) ≤ Real.sqrt (1 + ‖y‖) / 32 by positivity)
  linarith

/-- The hypothesis of `lem:glue` that the balls `B_j` lie in `4B`: it holds
for every cube of side `sigma(y) / 32` that meets the closed ball `2B`, when
`sigma_0 <= 10 rho`. -/
theorem lattice_covering_ball_subset {x0 y : LatticeSpace} {ρ : ℝ}
    (hρ : Real.sqrt (1 + ‖x0‖) / 10 ≤ ρ)
    (h : (cube y (Real.sqrt (1 + ‖y‖) / 32) ∩ closedBall x0 (2 * ρ)).Nonempty) :
    ball y (27 / 10 * (Real.sqrt (1 + ‖y‖) / 32)) ⊆ ball x0 (4 * ρ) := by
  have hy := lattice_covering_sigma_one_le y
  have h0 := lattice_covering_sigma_one_le x0
  have hl := lattice_covering_side_le hρ h
  obtain ⟨p, hp1, hp2⟩ := h
  have d1 := lattice_covering_cube_dist (by positivity) hp1
  rw [mem_closedBall] at hp2
  have tri := dist_triangle y p x0
  rw [dist_comm y p] at tri
  apply ball_subset_ball'
  linarith

/-! ### Existence of the covering -/

/-- **Selection.** For every ball there is a set of centres in the closed
ball `2B` whose cubes of side `sigma / 96` are pairwise disjoint and whose
cubes of side `sigma / 32` cover the closed ball `2B`. -/
theorem lattice_covering_selection (x0 : LatticeSpace) (ρ : ℝ) :
    ∃ u : Set LatticeSpace, u ⊆ closedBall x0 (2 * ρ) ∧
      u.PairwiseDisjoint (fun y => cube y (Real.sqrt (1 + ‖y‖) / 96)) ∧
      ∀ a ∈ closedBall x0 (2 * ρ), ∃ b ∈ u, a ∈ cube b (Real.sqrt (1 + ‖b‖) / 32) := by
  obtain ⟨u, hut, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun y : LatticeSpace => cube y (Real.sqrt (1 + ‖y‖) / 96)) (closedBall x0 (2 * ρ))
    (fun y => Real.sqrt (1 + ‖y‖)) 2 one_lt_two (fun a _ => Real.sqrt_nonneg _)
    (Real.sqrt (1 + ‖x0‖) + ρ)
    (fun a ha => by
      have h := lattice_covering_sigma_lipschitz a x0
      rw [mem_closedBall] at ha
      linarith)
    (fun a _ => ⟨a, cube_center_mem a (by positivity)⟩)
  refine ⟨u, hut, hdisj, fun a ha => ?_⟩
  obtain ⟨b, hb, ⟨p, hp1, hp2⟩, hab⟩ := hcov a ha
  refine ⟨b, hb, fun i => ?_⟩
  have a1 := hp1 i
  have a2 := hp2 i
  rw [abs_le] at a1 a2 ⊢
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- Pairwise disjoint cubes: no point lies in two of them. -/
theorem lattice_covering_small_overlap {u : Set LatticeSpace}
    (hdisj : u.PairwiseDisjoint (fun y => cube y (Real.sqrt (1 + ‖y‖) / 96)))
    (x : LatticeSpace) (T : Finset u)
    (hT : ∀ y ∈ T, x ∈ cube (y : LatticeSpace) (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96)) :
    T.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  have hne' : (a : LatticeSpace) ≠ (b : LatticeSpace) := fun h => hne (Subtype.ext h)
  exact Set.disjoint_left.mp (hdisj a.2 b.2 hne') (hT a ha) (hT b hb)

/-- **Finiteness.** A set of centres in a closed ball whose cubes of side
`sigma / 96` are pairwise disjoint is finite (volume count; the sides are at
least `1 / 96`). -/
theorem lattice_covering_finite {x0 : LatticeSpace} {ρ : ℝ} {u : Set LatticeSpace}
    (hu : u ⊆ closedBall x0 (2 * ρ))
    (hdisj : u.PairwiseDisjoint (fun y => cube y (Real.sqrt (1 + ‖y‖) / 96))) : u.Finite := by
  by_contra hinf
  have hI : Infinite u := Set.infinite_coe_iff.mpr hinf
  obtain ⟨y0, hy0⟩ : u.Nonempty := (Set.Infinite.nonempty hinf)
  have hρ0 : 0 ≤ 2 * ρ := dist_nonneg.trans (mem_closedBall.mp (hu hy0))
  have h0 := lattice_covering_sigma_one_le x0
  have hr : 0 ≤ 4 * ρ + (Real.sqrt (1 + ‖x0‖) + ρ) / 96 := by linarith
  have hbound : ∀ T : Finset u,
      (T.card : ℝ) * (1 / 96 : ℝ) ^ 3 ≤
        ((1 : ℕ) : ℝ) * (4 * ρ + (Real.sqrt (1 + ‖x0‖) + ρ) / 96) ^ 3 := by
    intro T
    refine cube_card_mul_pow_le T (fun y : u => (y : LatticeSpace))
      (fun y : u => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96) 1
      (lattice_covering_small_overlap hdisj) x0 hr ?_ (by norm_num) ?_
    · intro y _ z hz i
      have hy := mem_closedBall.mp (hu y.2)
      have lip := lattice_covering_sigma_lipschitz (y : LatticeSpace) x0
      have a1 := hz i
      have a2 : |(y : LatticeSpace) i - x0 i| ≤ dist (y : LatticeSpace) x0 := by
        have h := cube_closedBall_subset x0 (2 * dist (y : LatticeSpace) x0)
          (show (y : LatticeSpace) ∈ closedBall x0 (2 * dist (y : LatticeSpace) x0 / 2) by
            rw [mem_closedBall]
            linarith) i
        linarith
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    · intro y _
      have hy := lattice_covering_sigma_one_le (y : LatticeSpace)
      linarith
  obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq u
    (⌊(96 : ℝ) ^ 3 * (4 * ρ + (Real.sqrt (1 + ‖x0‖) + ρ) / 96) ^ 3⌋₊ + 1)
  have h1 := hbound T
  have h2 := Nat.lt_floor_add_one ((96 : ℝ) ^ 3 * (4 * ρ + (Real.sqrt (1 + ‖x0‖) + ρ) / 96) ^ 3)
  rw [hT] at h1
  push_cast at h1
  linarith

/-- **Overlap.** For centres whose cubes of side `sigma / 96` are pairwise
disjoint, a point lies in at most `(8 kappa)^3` of the cubes of side
`kappa * sigma / 96`, for `1 < kappa <= 64`. -/
theorem lattice_covering_overlap {u : Set LatticeSpace}
    (hdisj : u.PairwiseDisjoint (fun y => cube y (Real.sqrt (1 + ‖y‖) / 96)))
    {κ : ℝ} (hκ : 1 < κ) (hκ64 : κ ≤ 64) (x : LatticeSpace) (T : Finset u)
    (hT : ∀ y ∈ T, x ∈ cube (y : LatticeSpace)
      (κ * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96))) :
    (T.card : ℝ) ≤ (8 * κ) ^ 3 := by
  have h := cube_enlarged_overlap_card_le hκ (c := fun y : u => (y : LatticeSpace))
    (s := fun y : u => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96) (fun y => by positivity)
    (N0 := 1) (lattice_covering_small_overlap hdisj) (Λ := 2)
    (fun i j hij => by
      have hi := lattice_covering_sigma_one_le (i : LatticeSpace)
      have hj := lattice_covering_sigma_one_le (j : LatticeSpace)
      have h1 := lattice_covering_sigma_of_meet (t := κ / 96) (by positivity) (by positivity)
        (by linarith) (by linarith) hij
      have h2 := mul_le_mul_of_nonneg_right hκ64
        (show (0:ℝ) ≤ Real.sqrt (1 + ‖(i : LatticeSpace)‖) by positivity)
      have h3 := mul_le_mul_of_nonneg_right hκ64
        (show (0:ℝ) ≤ Real.sqrt (1 + ‖(j : LatticeSpace)‖) by positivity)
      linarith) x T hT
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- For any family of cubes of side `sigma(centre) / 32`, whatever its
construction: bounded overlap of the cubes gives bounded overlap of the balls
`B(c_i, 2.7 l_i)`. `lem:glue` asks for both; the paragraph "Large balls"
speaks of neither. -/
theorem lattice_covering_ball_overlap_of_cube_overlap {ι : Type*} (c : ι → LatticeSpace)
    {N0 : ℕ}
    (hN0 : ∀ x, ∀ T : Finset ι,
      (∀ i ∈ T, x ∈ cube (c i) (Real.sqrt (1 + ‖c i‖) / 32)) → T.card ≤ N0)
    (x : LatticeSpace) (T : Finset ι)
    (hT : ∀ i ∈ T, x ∈ ball (c i) (27 / 10 * (Real.sqrt (1 + ‖c i‖) / 32))) :
    (T.card : ℝ) ≤ N0 * (216 / 5) ^ 3 := by
  have h := cube_enlarged_overlap_card_le (κ := 27 / 5) (by norm_num) (c := c)
    (s := fun i => Real.sqrt (1 + ‖c i‖) / 32) (fun i => by positivity) hN0 (Λ := 2)
    (fun i j hij => by
      have hi := lattice_covering_sigma_one_le (c i)
      have hj := lattice_covering_sigma_one_le (c j)
      have h1 := lattice_covering_sigma_of_meet (t := 27 / 160) (by positivity) (by positivity)
        (by linarith) (by linarith) hij
      linarith) x T
    (fun i hi => ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (le_of_eq (by ring)))).trans
      (cube_closedBall_subset _ _)) (hT i hi))
  refine h.trans (le_of_eq ?_)
  ring

/-! ### The covering handed to the gluing lemma -/

/-- **The covering of the paragraph "Large balls".** For every ball
`B(x_0, rho)` there is a finite set `u` of centres in the closed ball `2B`
such that the cubes `Q_y` of side `sigma(y) / 32`, `y` in `u`, cover the
closed ball `2B`, no point lies in more than `13824` of them, and no point
lies in more than `2176782` of the balls `B(y, 2.7 sigma(y) / 32)`. The cubes
of side `sigma(y) / 96` are pairwise disjoint. No condition on `rho`. -/
theorem lattice_covering_large_ball (x0 : LatticeSpace) (ρ : ℝ) :
    ∃ u : Set LatticeSpace, u.Finite ∧ u ⊆ closedBall x0 (2 * ρ) ∧
      u.PairwiseDisjoint (fun y => cube y (Real.sqrt (1 + ‖y‖) / 96)) ∧
      (∀ a ∈ closedBall x0 (2 * ρ), ∃ b ∈ u, a ∈ cube b (Real.sqrt (1 + ‖b‖) / 32)) ∧
      (∀ x, ∀ T : Finset u, (∀ y ∈ T, x ∈ cube (y : LatticeSpace)
        (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32)) → T.card ≤ 13824) ∧
      (∀ x, ∀ T : Finset u, (∀ y ∈ T, x ∈ ball (y : LatticeSpace)
        (27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32))) → T.card ≤ 2176782) := by
  obtain ⟨u, hu, hdisj, hcov⟩ := lattice_covering_selection x0 ρ
  refine ⟨u, lattice_covering_finite hu hdisj, hu, hdisj, hcov, ?_, ?_⟩
  · intro x T hT
    have h := lattice_covering_overlap hdisj (κ := 3) (by norm_num) (by norm_num) x T
      (fun y hy => by
        have h1 := hT y hy
        rwa [show Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32 =
          3 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96) by ring] at h1)
    have h2 : (T.card : ℝ) ≤ ((13824 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · intro x T hT
    have h := lattice_covering_overlap hdisj (κ := 81 / 5) (by norm_num) (by norm_num) x T
      (fun y hy => by
        have h1 := hT y hy
        have h2 : ball (y : LatticeSpace) (27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32)) ⊆
            cube (y : LatticeSpace) (81 / 5 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 96)) := by
          refine (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)).trans
            (cube_closedBall_subset _ _)
          linarith [lattice_covering_sigma_one_le (y : LatticeSpace)]
        exact h2 h1)
    have h3 : (T.card : ℝ) < 2176783 := by
      norm_num at h
      linarith
    have h4 : T.card < 2176783 := by exact_mod_cast h3
    omega

/-- **The covering in the form the gluing lemma asks for.** For every ball
`B = B(x_0, rho)` with `sigma(x_0) <= 10 rho` there is a finite set `u` of
centres such that the cubes `Q_y` of side `l_y = sigma(y) / 32`, `y` in `u`,
and the balls `B_y = B(y, 2.7 l_y)` satisfy every geometric hypothesis of
`gluing_lemma` in dimension three with enlargement factor `1.01`, overlap
bounds `13824` and `2176782`, side ratio `1.03` and radius ratio `2.7`:
positive sides; the cubes cover the closed ball `2B`; bounded overlap of the
cubes; `sqrt 3 * l_y <= rho`; comparable sides of neighbours; `B_j` contains
the enlarged cubes of the neighbours of `j`; `B_y` lies in `4B`; bounded
overlap of the balls; and each `B_y` is a small ball, of positive radius at
most `sigma(y) / 10`. The constants do not depend on the ball. -/
theorem lattice_covering_gluing_hypotheses (x0 : LatticeSpace) {ρ : ℝ}
    (hρ : Real.sqrt (1 + ‖x0‖) / 10 ≤ ρ) :
    ∃ u : Set LatticeSpace, u.Finite ∧
      (∀ y : u, 0 < Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ∧
      closedBall x0 (2 * ρ) ⊆
        ⋃ y : u, cube (y : LatticeSpace) (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ∧
      (∀ x, ∀ T : Finset u, (∀ y ∈ T, x ∈ cube (y : LatticeSpace)
        (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32)) → T.card ≤ 13824) ∧
      (∀ y : u, Real.sqrt ((3 : ℕ) : ℝ) * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ≤ ρ) ∧
      (∀ i j : u, cubeNeighbor (101 / 100) (fun y : u => (y : LatticeSpace))
          (fun y : u => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) i j →
        Real.sqrt (1 + ‖(i : LatticeSpace)‖) / 32 ≤
          103 / 100 * (Real.sqrt (1 + ‖(j : LatticeSpace)‖) / 32)) ∧
      (∀ i j : u, cubeNeighbor (101 / 100) (fun y : u => (y : LatticeSpace))
          (fun y : u => Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) i j →
        cube (i : LatticeSpace) (101 / 100 * (Real.sqrt (1 + ‖(i : LatticeSpace)‖) / 32)) ⊆
          ball (j : LatticeSpace) (27 / 10 * (Real.sqrt (1 + ‖(j : LatticeSpace)‖) / 32))) ∧
      (∀ y : u, ball (y : LatticeSpace) (27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32)) ⊆
        ball x0 (4 * ρ)) ∧
      (∀ x, ∀ T : Finset u, (∀ y ∈ T, x ∈ ball (y : LatticeSpace)
        (27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32))) → T.card ≤ 2176782) ∧
      (∀ y : u, 0 < 27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ∧
        27 / 10 * (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ≤
          Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 10) := by
  obtain ⟨u, hfin, hu, -, hcov, hN0, hNb⟩ := lattice_covering_large_ball x0 ρ
  have hmeet : ∀ y : u, (cube (y : LatticeSpace) (Real.sqrt (1 + ‖(y : LatticeSpace)‖) / 32) ∩
      closedBall x0 (2 * ρ)).Nonempty :=
    fun y => ⟨y, cube_center_mem _ (by positivity), hu y.2⟩
  refine ⟨u, hfin, fun y => by positivity, ?_, hN0, ?_,
    fun i j hij => lattice_covering_neighbor_sides (y := i) (z := j) hij,
    fun i j hij => lattice_covering_neighbor_subset_ball (y := i) (z := j) hij,
    fun y => lattice_covering_ball_subset hρ (hmeet y), hNb,
    fun y => ⟨by positivity, (lattice_covering_ball_radius_lt y).le⟩⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hab⟩
  · intro y
    rw [Nat.cast_ofNat]
    exact (lattice_covering_diam_lt hρ (hmeet y)).le

end BrownRadial
