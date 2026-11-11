import LatticeSeparation
import LatticeVolume

/-!
Local comparison and cell mass for the lattice weight: the pointwise and mass
estimates used in the proof of `thm:B`(a) before any Poincare inequality
enters (paper, paragraphs "Local comparison" and "Cell mass").

Notation of the paper: `sigma(x)^2 = 1 + |x|`, `s_k = sqrt (2^k)`, shell `k`
is `2^k <= |x| < 2^(k+1)`, `d = dist(., Gamma)`, `d_C = dist(., C)`.

Part A (pointwise): the clearances of the other circles from a small ball,
the comparison `w ~ sigma_0^(-alpha) (1 + d_C^2)^(alpha/2)` near a circle,
the bounded oscillation of `w` away from the circles, and the bound near the
origin.

Part B (mass): `mu(B) >= c |B|` for every ball of radius at least a fixed
multiple of `sigma` at its centre, by a three-translate argument that uses
only that each circle is horizontal and that distinct circles are separated.
No doubling or Poincare inequality is claimed here.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### Shells and scales -/

/-- A point of norm at least 16 lies in a dyadic shell `k >= 4`. -/
theorem lattice_local_shell_exists {x : LatticeSpace} (hx : 16 ≤ ‖x‖) :
    ∃ k : ℕ, 4 ≤ k ∧ (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(k+1) := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1:ℝ) ≤ ‖x‖)
    (by norm_num : (1:ℝ) < 2)
  refine ⟨n, ?_, hn1, hn2⟩
  by_contra h
  have h5 : n + 1 ≤ 4 := by omega
  have h16 : (2:ℝ)^(n+1) ≤ (2:ℝ)^4 := pow_le_pow_right₀ (by norm_num) h5
  norm_num at h16
  linarith

/-- `s_k >= 4` from shell four on. -/
theorem lattice_local_scale_ge {k : ℕ} (hk : 4 ≤ k) : 4 ≤ Real.sqrt ((2:ℝ)^k) := by
  have h16 : (2:ℝ)^4 ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  norm_num at h16 ⊢
  exact h16

/-- Paper: `sigma >= s_k` on shell `k`. -/
theorem lattice_local_sigma_ge {k : ℕ} {x : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖x‖) :
    Real.sqrt ((2:ℝ)^k) ≤ Real.sqrt (1 + ‖x‖) :=
  Real.sqrt_le_sqrt (by linarith)

/-- Paper: `sigma <= 1.44 s_k` on shell `k >= 4`. -/
theorem lattice_local_sigma_le {k : ℕ} (hk : 4 ≤ k) {x : LatticeSpace}
    (h2 : ‖x‖ < (2:ℝ)^(k+1)) :
    Real.sqrt (1 + ‖x‖) ≤ (144/100 : ℝ) * Real.sqrt ((2:ℝ)^k) := by
  have h16 : (2:ℝ)^4 ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [pow_succ] at h2
  norm_num at h16 ⊢
  linarith

/-- Paper: a small ball, `rho <= sigma_0 / 10`, has `rho <= 0.15 s_k`. -/
theorem lattice_local_radius_le {k : ℕ} (hk : 4 ≤ k) {x : LatticeSpace}
    (h2 : ‖x‖ < (2:ℝ)^(k+1)) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x‖) / 10) :
    ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k) := by
  have h := lattice_local_sigma_le hk h2
  have hS : 0 ≤ Real.sqrt ((2:ℝ)^k) := Real.sqrt_nonneg _
  linarith

theorem lattice_local_norm_dist {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a‖ ≤ ‖b‖ + dist a b ∧ ‖b‖ ≤ ‖a‖ + dist a b := by
  have h := abs_norm_sub_norm_le a b
  rw [← dist_eq_norm] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-! ### Membership in the valleys -/

theorem lattice_local_valley_mem {q : LatticeSpace} (hq : q ∈ latticeValleys) :
    ∃ k : ℕ, 4 ≤ k ∧ ∃ i : Fin (latticeLayerCount k), ∃ j : Fin (latticeCirclesPerLayer k),
      q ∈ indexedLatticeCircle k i j := by
  obtain ⟨⟨k, hk⟩, hq⟩ := mem_iUnion.mp hq
  obtain ⟨i, hq⟩ := mem_iUnion.mp hq
  obtain ⟨j, hq⟩ := mem_iUnion.mp hq
  exact ⟨k, hk, i, j, hq⟩

theorem lattice_local_circle_subset {k : ℕ} (hk : 4 ≤ k) (i : Fin (latticeLayerCount k))
    (j : Fin (latticeCirclesPerLayer k)) : indexedLatticeCircle k i j ⊆ latticeValleys :=
  fun _ hz => mem_iUnion.mpr ⟨⟨k, hk⟩, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hz⟩⟩⟩

theorem lattice_local_circle_nonempty (k : ℕ) (i : Fin (latticeLayerCount k))
    (j : Fin (latticeCirclesPerLayer k)) : (indexedLatticeCircle k i j).Nonempty :=
  latitudeCircle_nonempty (le_trans (by positivity) (latticeCircleRadius_bounds k i).1) _

/-! ### Separation statements of the paper, in the form used below -/

/-- Paper: "within shell `m` the layers are at least `s_m / sqrt 2` apart
radially", in squared form: the radial mesh `2^m / L_m` has square at least
`2^m / 2`. -/
theorem lattice_local_mesh_sq_ge (m : ℕ) :
    (2:ℝ)^m / 2 ≤ ((2:ℝ)^m / latticeLayerCount m)^2 := by
  rw [lattice_radial_mesh, ← pow_mul]
  have hk : m ≤ m / 2 * 2 + 1 := by omega
  have hp : (2:ℝ)^m ≤ (2:ℝ)^(m / 2 * 2 + 1) := pow_le_pow_right₀ (by norm_num) hk
  rw [pow_succ] at hp
  linarith

/-- Paper: "the radial gap below shell `k` can be as small as `s_k / 2`": for
even `k` the mesh of shell `k - 1` equals `s_k / 2` exactly. -/
theorem lattice_local_mesh_eq_half_scale (m : ℕ) :
    (2:ℝ)^(2*m+1) / latticeLayerCount (2*m+1) = Real.sqrt ((2:ℝ)^(2*m+2)) / 2 := by
  rw [lattice_radial_mesh]
  have h1 : (2*m+1)/2 = m := by omega
  have h2 : (2:ℝ)^(2*m+2) = ((2:ℝ)^(m+1))^2 := by rw [← pow_mul]; congr 1; ring
  rw [h1, h2, Real.sqrt_sq (by positivity), pow_succ]
  ring

/-- Paper: every circle of a shell below `k` lies in
`{|x| <= 2^k - s_k / 2}`. -/
theorem lattice_local_lower_shell_norm_le {k k' : ℕ} (hkk : k' < k)
    (i : Fin (latticeLayerCount k')) (j : Fin (latticeCirclesPerLayer k')) {q : LatticeSpace}
    (hq : q ∈ indexedLatticeCircle k' i j) :
    ‖q‖ ≤ (2:ℝ)^k - Real.sqrt ((2:ℝ)^k) / 2 := by
  rw [show ‖q‖ = latticeCircleRadius k' i from hq.1]
  have hup := latticeCircleRadius_upper_gap k' i
  rw [lattice_radial_mesh] at hup
  rcases Nat.lt_or_ge (k'+1) k with h | h
  · have hp : (2:ℝ)^(k'+1) ≤ (2:ℝ)^(k-1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hT : (2:ℝ)^k = 2 * (2:ℝ)^(k-1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hS : Real.sqrt ((2:ℝ)^k) ≤ (2:ℝ)^k := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      nlinarith
    have hpos : (0:ℝ) < (2:ℝ)^(k'/2) := by positivity
    linarith
  · have hk : k = k' + 1 := by omega
    subst hk
    have hS : Real.sqrt ((2:ℝ)^(k'+1)) / 2 ≤ (2:ℝ)^(k'/2) := by
      rw [div_le_iff₀ (by norm_num), Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, ← pow_mul]
      have hk2 : k' ≤ k'/2*2 + 1 := by omega
      have hp : (2:ℝ)^k' ≤ (2:ℝ)^(k'/2*2+1) := pow_le_pow_right₀ (by norm_num) hk2
      rw [pow_succ] at hp ⊢
      nlinarith [show (0:ℝ) < (2:ℝ)^(k'/2*2) by positivity]
    linarith

/-- Paper: two distinct circles lying in shells `>= k` are at distance at
least `0.7 s_k`. Stated for points: either the second point lies on the
circle of the first, or the two points are `0.7 s_k` apart. -/
theorem lattice_local_circles_separated {k k1 k2 : ℕ} (hk : 4 ≤ k) (h1 : k ≤ k1) (h2 : k ≤ k2)
    (i1 : Fin (latticeLayerCount k1)) (j1 : Fin (latticeCirclesPerLayer k1))
    (i2 : Fin (latticeLayerCount k2)) (j2 : Fin (latticeCirclesPerLayer k2))
    {p q : LatticeSpace} (hp : p ∈ indexedLatticeCircle k1 i1 j1)
    (hq : q ∈ indexedLatticeCircle k2 i2 j2) :
    q ∈ indexedLatticeCircle k1 i1 j1 ∨ (7/10 : ℝ) * Real.sqrt ((2:ℝ)^k) ≤ dist p q := by
  have hmono : ∀ m : ℕ, k ≤ m →
      (7/10 : ℝ) * Real.sqrt ((2:ℝ)^k) ≤ (7/10 : ℝ) * Real.sqrt ((2:ℝ)^m) := by
    intro m hm
    have h : (2:ℝ)^k ≤ (2:ℝ)^m := pow_le_pow_right₀ (by norm_num) hm
    have h' := Real.sqrt_le_sqrt h
    linarith
  rcases lt_trichotomy k1 k2 with h | h | h
  · right
    exact (hmono k1 h1).trans (lattice_distinct_shells_separated h i1 j1 i2 j2 hp hq)
  · subst h
    by_cases he : (i1, j1) = (i2, j2)
    · left
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hq
    · right
      exact (hmono k1 h1).trans (lattice_same_shell_separated k1 (hk.trans h1) he hp hq)
  · right
    rw [dist_comm]
    exact (hmono k2 h2).trans (lattice_distinct_shells_separated h i2 j2 i1 j1 hq hp)

/-! ### Clearances from a small ball -/

/-- Paper: the circles of shells below `k` are at distance at least
`s_k / 2 - rho >= 0.35 s_k` from a small ball centred in shell `k`. -/
theorem lattice_local_lower_shell_clearance {k k2 : ℕ} (hkk : k2 < k)
    (i2 : Fin (latticeLayerCount k2)) (j2 : Fin (latticeCirclesPerLayer k2))
    {x0 y q : LatticeSpace} {ρ : ℝ} (h1 : (2:ℝ)^k ≤ ‖x0‖)
    (hρ : ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k)) (hy : dist y x0 < ρ)
    (hq : q ∈ indexedLatticeCircle k2 i2 j2) :
    (7/20 : ℝ) * Real.sqrt ((2:ℝ)^k) ≤ dist y q := by
  have hn := lattice_local_lower_shell_norm_le hkk i2 j2 hq
  have h3 := (lattice_local_norm_dist y x0).2
  have h4 := (lattice_local_norm_dist y q).1
  linarith

/-- The nearest circle to the centre of a small ball in the near case lies in
a shell `>= k` (paper: "then `C` lies in shell `k` or `k+1`"; only the lower
bound is needed). -/
theorem lattice_local_nearest_shell_ge {k k' : ℕ} (i : Fin (latticeLayerCount k'))
    (j : Fin (latticeCirclesPerLayer k')) {x0 c : LatticeSpace} {ρ : ℝ}
    (h1 : (2:ℝ)^k ≤ ‖x0‖) (hρ : ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k))
    (hc : c ∈ indexedLatticeCircle k' i j) (hcd : dist x0 c ≤ 2 * ρ) : k ≤ k' := by
  by_contra h
  have hn := lattice_local_lower_shell_norm_le (not_le.mp h) i j hc
  have h3 := (lattice_local_norm_dist x0 c).1
  have hS : 0 < Real.sqrt ((2:ℝ)^k) := Real.sqrt_pos.mpr (by positivity)
  linarith

/-- Paper: every circle other than the nearest one stays at distance at least
`0.25 s_k` from the small ball (`0.7 s_k - 3 rho >= 0.25 s_k` for the shells
`>= k`, `0.35 s_k` for the shells below). -/
theorem lattice_local_other_circle_clearance {k k' : ℕ} (hk : 4 ≤ k) (hkk : k ≤ k')
    (i : Fin (latticeLayerCount k')) (j : Fin (latticeCirclesPerLayer k'))
    {x0 c y q : LatticeSpace} {ρ : ℝ} (h1 : (2:ℝ)^k ≤ ‖x0‖)
    (hρ : ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k))
    (hc : c ∈ indexedLatticeCircle k' i j) (hcd : dist x0 c ≤ 2 * ρ)
    (hy : dist y x0 < ρ) (hq : q ∈ latticeValleys) :
    q ∈ indexedLatticeCircle k' i j ∨ Real.sqrt ((2:ℝ)^k) / 4 ≤ dist y q := by
  obtain ⟨k2, _, i2, j2, hq2⟩ := lattice_local_valley_mem hq
  have hS : 0 < Real.sqrt ((2:ℝ)^k) := Real.sqrt_pos.mpr (by positivity)
  rcases Nat.lt_or_ge k2 k with h | h
  · right
    have h5 := lattice_local_lower_shell_clearance h i2 j2 h1 hρ hy hq2
    linarith
  · rcases lattice_local_circles_separated hk hkk h i j i2 j2 hc hq2 with h' | h'
    · left
      exact h'
    · right
      have t1 := dist_triangle c x0 q
      have t2 := dist_triangle x0 y q
      rw [dist_comm c x0] at t1
      rw [dist_comm x0 y] at t2
      linarith

/-- Paper: in the near case, on the small ball, `d = d_C` where
`d_C <= 0.25 s_k`, and elsewhere both lie in `[0.25 s_k, 3 rho]`, with
`3 rho <= 0.45 s_k`. Here `C` is any circle nearest to the centre. -/
theorem lattice_local_near_distances {k : ℕ} (hk : 4 ≤ k) {x0 : LatticeSpace}
    (h1 : (2:ℝ)^k ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k))
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ) (k' : ℕ)
    (i : Fin (latticeLayerCount k')) (j : Fin (latticeCirclesPerLayer k'))
    (hC : infDist x0 (indexedLatticeCircle k' i j) = infDist x0 latticeValleys)
    {y : LatticeSpace} (hy : y ∈ ball x0 ρ) :
    infDist y latticeValleys ≤ infDist y (indexedLatticeCircle k' i j) ∧
    min (infDist y (indexedLatticeCircle k' i j)) (Real.sqrt ((2:ℝ)^k) / 4) ≤
      infDist y latticeValleys ∧
    infDist y (indexedLatticeCircle k' i j) < 3 * ρ ∧
    3 * ρ ≤ (9/20 : ℝ) * Real.sqrt ((2:ℝ)^k) := by
  rw [mem_ball] at hy
  have hne := lattice_local_circle_nonempty k' i j
  obtain ⟨c, hc, hcd⟩ : ∃ c ∈ indexedLatticeCircle k' i j,
      infDist x0 (indexedLatticeCircle k' i j) = dist x0 c :=
    (latitudeCircle_isCompact _ _).exists_infDist_eq_dist hne x0
  have hcd' : dist x0 c ≤ 2 * ρ := by
    rw [← hcd, hC]
    exact hnear
  have hkk := lattice_local_nearest_shell_ge i j h1 hρ hc hcd'
  have hsub := lattice_local_circle_subset (hk.trans hkk) i j
  refine ⟨infDist_le_infDist_of_subset hsub hne, ?_, ?_, by linarith⟩
  · rw [le_infDist latticeValleys_nonempty]
    intro q hq
    rcases lattice_local_other_circle_clearance hk hkk i j h1 hρ hc hcd' hy hq with h | h
    · exact (min_le_left _ _).trans (infDist_le_dist_of_mem h)
    · exact (min_le_right _ _).trans h
  · have t := dist_triangle y x0 c
    have h := infDist_le_dist_of_mem (x := y) hc
    linarith

/-! ### Near case: the comparison `(eq:wcompare)` -/

/-- Scalar form of the near-case comparison. With `n0 = |x_0|`, `n = |y|`,
`d` and `dC` the two distances: the base `(1+d^2)/(1+n+d^2)` of the weight is
between `1/4` and `2` times `(1+dC^2)/(1+n0)`. The intermediate bounds are
those of the paper: `1+n >= sigma_0^2/2` and `1+n+d^2 <= 2 sigma_0^2`. -/
theorem lattice_local_near_scalar {n0 n d dC ρ : ℝ} (hn0 : 0 ≤ n0)
    (hρ : 100 * ρ^2 ≤ 1 + n0) (hρ0 : 0 < ρ) (hn1 : n0 ≤ n + ρ) (hn2 : n ≤ n0 + ρ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ dC) (hd2 : dC ≤ 9/5 * d) (hd3 : dC < 3 * ρ) :
    (1 + n0) / 2 ≤ 1 + n ∧ 1 + n + d^2 ≤ 2 * (1 + n0) ∧
    1/4 * ((1 + dC^2) / (1 + n0)) ≤ (1 + d^2) / (1 + n + d^2) ∧
    (1 + d^2) / (1 + n + d^2) ≤ 2 * ((1 + dC^2) / (1 + n0)) := by
  have hρ1 : 10 * ρ ≤ 1 + n0 := by
    by_contra h
    have h' : 1 + n0 < 10 * ρ := not_le.mp h
    nlinarith
  have hdC0 : 0 ≤ dC := hd0.trans hd1
  have hd3' : dC^2 ≤ 9 * ρ^2 := by nlinarith
  have hd4 : d^2 ≤ dC^2 := pow_le_pow_left₀ hd0 hd1 2
  have hd5 : dC^2 ≤ (81/25) * d^2 := by
    have h := pow_le_pow_left₀ hdC0 hd2 2
    rw [mul_pow] at h
    norm_num at h
    exact h
  have hD0 : 0 < 1 + n + d^2 := by nlinarith
  have hσ : 0 < 1 + n0 := by linarith
  have hup : 1 + n + d^2 ≤ (119/100) * (1 + n0) := by nlinarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [← mul_div_assoc, div_le_div_iff₀ hσ hD0]
    have hA : 1 + dC^2 ≤ (81/25) * (1 + d^2) := by nlinarith
    have hpos : 0 ≤ 1 + d^2 := by positivity
    nlinarith [mul_le_mul hA hup hD0.le (by positivity : (0:ℝ) ≤ (81/25) * (1 + d^2))]
  · rw [← mul_div_assoc, div_le_div_iff₀ hD0 hσ]
    have hA : 1 + d^2 ≤ 1 + dC^2 := by linarith
    have hB : 1 + n0 ≤ 2 * (1 + n + d^2) := by nlinarith
    have hpos : 0 ≤ 1 + dC^2 := by positivity
    nlinarith [mul_le_mul hA hB hσ.le hpos]

theorem lattice_local_profile_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (β : ℝ) :
    (a / b)^β = b^(-β) * a^β := by
  rw [Real.div_rpow ha hb.le, Real.rpow_neg hb.le, div_eq_mul_inv, mul_comm]

/-- **Near case, `(eq:wcompare)`.** Let `|x_0| >= 16`, `rho <= sigma_0 / 10`
and `dist(x_0, Gamma) <= 2 rho`. For every lattice circle `C` nearest to
`x_0` and every `y` in `B(x_0, rho)`,
`4^(-alpha/2) sigma_0^(-alpha) (1 + d_C(y)^2)^(alpha/2) <= w(y) <=
2^(alpha/2) sigma_0^(-alpha) (1 + d_C(y)^2)^(alpha/2)`. -/
theorem lattice_local_near_comparison {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10)
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ) (k' : ℕ)
    (i : Fin (latticeLayerCount k')) (j : Fin (latticeCirclesPerLayer k'))
    (hC : infDist x0 (indexedLatticeCircle k' i j) = infDist x0 latticeValleys)
    {y : LatticeSpace} (hy : y ∈ ball x0 ρ) :
    (1/4 : ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
        (1 + (infDist y (indexedLatticeCircle k' i j))^2)^(α/2)) ≤
      latticeWeight latticeValleys α y ∧
    latticeWeight latticeValleys α y ≤
      (2:ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
        (1 + (infDist y (indexedLatticeCircle k' i j))^2)^(α/2)) := by
  obtain ⟨k, hk, h1, h2⟩ := lattice_local_shell_exists hx0
  have hρk := lattice_local_radius_le hk h2 hρ
  obtain ⟨hd1, hd2, hd3, hd4⟩ := lattice_local_near_distances hk h1 hρk hnear k' i j hC hy
  rw [mem_ball] at hy
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg hy
  have hσ0 : 0 < 1 + ‖x0‖ := by positivity
  have hρsq : 100 * ρ^2 ≤ 1 + ‖x0‖ := by
    have h := pow_le_pow_left₀ hρ0.le hρ 2
    rw [div_pow, Real.sq_sqrt hσ0.le] at h
    linarith
  have hnd := lattice_local_norm_dist y x0
  have hd0 : 0 ≤ infDist y latticeValleys := infDist_nonneg
  have hd5 : infDist y (indexedLatticeCircle k' i j) ≤ 9/5 * infDist y latticeValleys := by
    rcases le_total (infDist y (indexedLatticeCircle k' i j)) (Real.sqrt ((2:ℝ)^k) / 4) with h | h
    · rw [min_eq_left h] at hd2
      linarith
    · rw [min_eq_right h] at hd2
      linarith
  obtain ⟨-, -, hlow, hupp⟩ := lattice_local_near_scalar (norm_nonneg x0) hρsq hρ0
    (by linarith [hnd.2]) (by linarith [hnd.1]) hd0 hd1 hd5 hd3
  have hC0 : 0 ≤ 1 + (infDist y (indexedLatticeCircle k' i j))^2 := by positivity
  have hX0 : 0 ≤ (1 + (infDist y (indexedLatticeCircle k' i j))^2) / (1 + ‖x0‖) :=
    div_nonneg hC0 hσ0.le
  have hα2 : 0 ≤ α/2 := by positivity
  rw [← lattice_local_profile_rpow hC0 hσ0, ← Real.mul_rpow (by norm_num) hX0,
    ← Real.mul_rpow (by norm_num) hX0]
  unfold latticeWeight
  exact ⟨Real.rpow_le_rpow (by positivity) hlow hα2, Real.rpow_le_rpow (by positivity) hupp hα2⟩

/-- Near case with an existential circle, on `B(x_0, rho)`. -/
theorem lattice_local_near_comparison_exists {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10)
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ) :
    ∃ k' : {k : ℕ // 4 ≤ k}, ∃ i : Fin (latticeLayerCount k'.val),
      ∃ j : Fin (latticeCirclesPerLayer k'.val),
        infDist x0 (indexedLatticeCircle k'.val i j) = infDist x0 latticeValleys ∧
        ∀ y ∈ ball x0 ρ,
          (1/4 : ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
              (1 + (infDist y (indexedLatticeCircle k'.val i j))^2)^(α/2)) ≤
            latticeWeight latticeValleys α y ∧
          latticeWeight latticeValleys α y ≤
            (2:ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
              (1 + (infDist y (indexedLatticeCircle k'.val i j))^2)^(α/2)) := by
  obtain ⟨k', i, j, hC⟩ := lattice_nearest_circle x0
  exact ⟨k', i, j, hC, fun y hy =>
    lattice_local_near_comparison hα hx0 hρ hnear k'.val i j hC hy⟩

/-- Near case on the doubled ball: if `rho <= sigma_0 / 20` and
`dist(x_0, Gamma) <= 2 rho`, one circle serves on all of `B(x_0, 2 rho)`
(hence also on `B(x_0, rho)`), with the same constants. -/
theorem lattice_local_near_comparison_double {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 20)
    (hnear : infDist x0 latticeValleys ≤ 2 * ρ) :
    ∃ k' : {k : ℕ // 4 ≤ k}, ∃ i : Fin (latticeLayerCount k'.val),
      ∃ j : Fin (latticeCirclesPerLayer k'.val),
        infDist x0 (indexedLatticeCircle k'.val i j) = infDist x0 latticeValleys ∧
        ∀ y ∈ ball x0 (2 * ρ),
          (1/4 : ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
              (1 + (infDist y (indexedLatticeCircle k'.val i j))^2)^(α/2)) ≤
            latticeWeight latticeValleys α y ∧
          latticeWeight latticeValleys α y ≤
            (2:ℝ)^(α/2) * ((1 + ‖x0‖)^(-(α/2)) *
              (1 + (infDist y (indexedLatticeCircle k'.val i j))^2)^(α/2)) := by
  have h0 : 0 ≤ infDist x0 latticeValleys := infDist_nonneg
  exact lattice_local_near_comparison_exists hα hx0 (by linarith) (by linarith)

/-! ### Far case: bounded oscillation -/

/-- The monotonicity of `(1+t)/(1+n+t)` in `t` and `n`, in the form used for
the far case. -/
theorem lattice_local_ratio_core {P Q ny nz K e : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hny : 0 ≤ ny) (hnz : 0 ≤ nz) (hPQ : P ≤ K * Q) (hn : nz ≤ ny + e)
    (he : e ≤ (K - 1) * Q) : P / (ny + P) ≤ K * (Q / (nz + Q)) := by
  have hA : 0 < ny + P := by linarith
  have hB : 0 < nz + Q := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ hA hB]
  have h1 : P * nz ≤ P * (ny + e) := mul_le_mul_of_nonneg_left hn hP.le
  have h2 : P * e ≤ P * ((K - 1) * Q) := mul_le_mul_of_nonneg_left he hP.le
  have h3 : P * ny ≤ K * Q * ny := mul_le_mul_of_nonneg_right hPQ hny
  nlinarith

/-- **Far case.** If `dist(x_0, Gamma) >= 2 rho`, then
`sup_{B(x_0, 2 rho)} w <= 16^(alpha/2) inf_{B(x_0, rho)} w`, for an arbitrary
closed or non-closed valley set in any normed space, with no restriction on
`rho` or on `x_0`. The paper states the constant `18^(alpha/2)` for small
balls in shells `k >= 4`. -/
theorem lattice_local_far_sup_le_inf {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {α : ℝ}
    (hα : 0 ≤ α) {x0 : E} {ρ : ℝ} (hfar : 2 * ρ ≤ infDist x0 Γ) {y z : E}
    (hy : y ∈ ball x0 (2 * ρ)) (hz : z ∈ ball x0 ρ) :
    latticeWeight Γ α y ≤ (16:ℝ)^(α/2) * latticeWeight Γ α z := by
  rw [mem_ball] at hy hz
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg hz
  have hdy : infDist y Γ ≤ infDist x0 Γ + dist y x0 := infDist_le_infDist_add_dist
  have hdz : infDist x0 Γ ≤ infDist z Γ + dist x0 z := infDist_le_infDist_add_dist
  rw [dist_comm x0 z] at hdz
  have hdy0 : 0 ≤ infDist y Γ := infDist_nonneg
  have hzy := dist_triangle z x0 y
  rw [dist_comm x0 y] at hzy
  have hnn := (lattice_local_norm_dist z y).1
  have hdz1 : ρ ≤ infDist z Γ := by linarith
  have h4 : infDist y Γ ≤ 4 * infDist z Γ := by linarith
  have hP : (1 + (infDist y Γ)^2) ≤ 16 * (1 + (infDist z Γ)^2) := by
    have h := pow_le_pow_left₀ hdy0 h4 2
    rw [mul_pow] at h
    nlinarith
  have hQ : 2 * ρ ≤ 1 + (infDist z Γ)^2 := by nlinarith [sq_nonneg (infDist z Γ - 1)]
  have hcore := lattice_local_ratio_core (K := 16) (e := 3 * ρ)
    (by positivity : (0:ℝ) < 1 + (infDist y Γ)^2) (by positivity : (0:ℝ) < 1 + (infDist z Γ)^2)
    (norm_nonneg y) (norm_nonneg z) hP (by linarith) (by linarith)
  unfold latticeWeight
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  rw [show 1 + ‖y‖ + (infDist y Γ)^2 = ‖y‖ + (1 + (infDist y Γ)^2) by ring,
    show 1 + ‖z‖ + (infDist z Γ)^2 = ‖z‖ + (1 + (infDist z Γ)^2) by ring]
  exact hcore

/-- Far case, oscillation on the ball itself: `w` varies on `B(x_0, rho)` by
a factor at most `9^(alpha/2)` (the paper says the base varies by a factor
`<= 81`). -/
theorem lattice_local_far_variation {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {α : ℝ}
    (hα : 0 ≤ α) {x0 : E} {ρ : ℝ} (hfar : 2 * ρ ≤ infDist x0 Γ) {y z : E}
    (hy : y ∈ ball x0 ρ) (hz : z ∈ ball x0 ρ) :
    latticeWeight Γ α y ≤ (9:ℝ)^(α/2) * latticeWeight Γ α z := by
  rw [mem_ball] at hy hz
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg hz
  have hdy : infDist y Γ ≤ infDist x0 Γ + dist y x0 := infDist_le_infDist_add_dist
  have hdz : infDist x0 Γ ≤ infDist z Γ + dist x0 z := infDist_le_infDist_add_dist
  rw [dist_comm x0 z] at hdz
  have hdy0 : 0 ≤ infDist y Γ := infDist_nonneg
  have hzy := dist_triangle z x0 y
  rw [dist_comm x0 y] at hzy
  have hnn := (lattice_local_norm_dist z y).1
  have hdz1 : ρ ≤ infDist z Γ := by linarith
  have h4 : infDist y Γ ≤ 3 * infDist z Γ := by linarith
  have hP : (1 + (infDist y Γ)^2) ≤ 9 * (1 + (infDist z Γ)^2) := by
    have h := pow_le_pow_left₀ hdy0 h4 2
    rw [mul_pow] at h
    nlinarith
  have hQ : 2 * ρ ≤ 1 + (infDist z Γ)^2 := by nlinarith [sq_nonneg (infDist z Γ - 1)]
  have hcore := lattice_local_ratio_core (K := 9) (e := 2 * ρ)
    (by positivity : (0:ℝ) < 1 + (infDist y Γ)^2) (by positivity : (0:ℝ) < 1 + (infDist z Γ)^2)
    (norm_nonneg y) (norm_nonneg z) hP (by linarith) (by linarith)
  unfold latticeWeight
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  rw [show 1 + ‖y‖ + (infDist y Γ)^2 = ‖y‖ + (1 + (infDist y Γ)^2) by ring,
    show 1 + ‖z‖ + (infDist z Γ)^2 = ‖z‖ + (1 + (infDist z Γ)^2) by ring]
  exact hcore

/-- The far case with the paper's constant `18^(alpha/2)`, for the lattice. -/
theorem lattice_local_far_sup_le_inf_paper {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace} {ρ : ℝ}
    (hfar : 2 * ρ < infDist x0 latticeValleys) {y z : LatticeSpace}
    (hy : y ∈ ball x0 (2 * ρ)) (hz : z ∈ ball x0 ρ) :
    latticeWeight latticeValleys α y ≤ (18:ℝ)^(α/2) * latticeWeight latticeValleys α z := by
  refine (lattice_local_far_sup_le_inf latticeValleys hα hfar.le hy hz).trans ?_
  apply mul_le_mul_of_nonneg_right _ (latticeWeight_pos _ _ _).le
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)

/-! ### Near the origin -/

/-- For any valley set, `w(x) >= (1 + |x|)^(-alpha/2)`. -/
theorem lattice_local_weight_ge_inv {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {α : ℝ}
    (hα : 0 ≤ α) (x : E) : (1 / (1 + ‖x‖))^(α/2) ≤ latticeWeight Γ α x := by
  have hpos : 0 < 1 + ‖x‖ := by positivity
  apply latticeWeight_lower Γ hα (by positivity)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  nlinarith [mul_nonneg (norm_nonneg x) (sq_nonneg (infDist x Γ))]

/-- **Near the origin.** On `{|x| <= 32}`, `33^(-alpha/2) <= w <= 1`. The
paper writes `34^(-alpha/2)`, which is weaker. -/
theorem lattice_local_near_origin {α : ℝ} (hα : 0 ≤ α) {x : LatticeSpace} (hx : ‖x‖ ≤ 32) :
    (1/33 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α x ∧
      latticeWeight latticeValleys α x ≤ 1 := by
  refine ⟨le_trans ?_ (lattice_local_weight_ge_inv latticeValleys hα x),
    latticeWeight_le_one latticeValleys hα x⟩
  apply Real.rpow_le_rpow (by norm_num) _ (by positivity)
  have hpos : 0 < 1 + ‖x‖ := by positivity
  rw [div_le_div_iff₀ (by norm_num) hpos]
  linarith

/-- The paper's constant `34^(-alpha/2)` on `{|x| <= 32}`. -/
theorem lattice_local_near_origin_paper {α : ℝ} (hα : 0 ≤ α) {x : LatticeSpace}
    (hx : ‖x‖ ≤ 32) : (1/34 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α x :=
  le_trans (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity))
    (lattice_local_near_origin hα hx).1

/-- `33` cannot be lowered: there is a point with `|x| = 32` (on the innermost
circle of shell five) where `w = 33^(-alpha/2)`. -/
theorem lattice_local_near_origin_sharp (α : ℝ) :
    ∃ x : LatticeSpace, ‖x‖ = 32 ∧ latticeWeight latticeValleys α x = (1/33 : ℝ)^(α/2) := by
  let i : Fin (latticeLayerCount 5) := ⟨0, by norm_num [latticeLayerCount]⟩
  let j : Fin (latticeCirclesPerLayer 5) := ⟨0, by norm_num [latticeCirclesPerLayer]⟩
  obtain ⟨x, hx⟩ := lattice_local_circle_nonempty 5 i j
  have hR : latticeCircleRadius 5 i = 32 := by
    simp only [latticeCircleRadius, i]
    norm_num
  have hn : ‖x‖ = 32 := by rw [show ‖x‖ = latticeCircleRadius 5 i from hx.1, hR]
  refine ⟨x, hn, ?_⟩
  unfold latticeWeight
  rw [infDist_zero_of_mem (lattice_local_circle_subset (by norm_num) i j hx), hn]
  norm_num

/-- Every point of the valleys has norm at least 16. -/
theorem lattice_cell_valley_norm_ge {q : LatticeSpace} (hq : q ∈ latticeValleys) : 16 ≤ ‖q‖ := by
  obtain ⟨k, hk, i, j, hq⟩ := lattice_local_valley_mem hq
  have h : (2:ℝ)^k ≤ ‖q‖ := (indexedLatticeCircle_in_shell k i j hq).1
  have h16 : (2:ℝ)^4 ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at h16
  linarith

/-- Paper's remark "the bound `d <= sigma_0` need not hold": at the origin
`d >= 16` while `sigma = 1`. -/
theorem lattice_local_origin_dist :
    Real.sqrt (1 + ‖(0 : LatticeSpace)‖) < infDist (0 : LatticeSpace) latticeValleys := by
  have h : (16:ℝ) ≤ infDist (0 : LatticeSpace) latticeValleys := by
    rw [le_infDist latticeValleys_nonempty]
    intro q hq
    rw [dist_zero_left]
    exact lattice_cell_valley_norm_ge hq
  rw [norm_zero, add_zero, Real.sqrt_one]
  linarith

/-- Paper, near case: `1 + |x| >= sigma_0^2 / 2` and
`1 + |x| + d^2 <= 2 sigma_0^2` on a small ball whose centre is within
`2 rho` of the valleys. Valid for any valley set. -/
theorem lattice_local_near_base_bounds {E : Type*} [NormedAddCommGroup E] (Γ : Set E)
    {x0 : E} {ρ : ℝ} (hρ : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10) (hnear : infDist x0 Γ ≤ 2 * ρ)
    {y : E} (hy : y ∈ ball x0 ρ) :
    (1 + ‖x0‖) / 2 ≤ 1 + ‖y‖ ∧ 1 + ‖y‖ + (infDist y Γ)^2 ≤ 2 * (1 + ‖x0‖) := by
  rw [mem_ball] at hy
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg hy
  have hσ0 : 0 < 1 + ‖x0‖ := by positivity
  have hρsq : 100 * ρ^2 ≤ 1 + ‖x0‖ := by
    have h := pow_le_pow_left₀ hρ0.le hρ 2
    rw [div_pow, Real.sq_sqrt hσ0.le] at h
    linarith
  have hρ1 : 10 * ρ ≤ 1 + ‖x0‖ := by
    by_contra h
    have h' : 1 + ‖x0‖ < 10 * ρ := not_le.mp h
    nlinarith [norm_nonneg x0]
  have hnd := lattice_local_norm_dist y x0
  have hd : infDist y Γ ≤ infDist x0 Γ + dist y x0 := infDist_le_infDist_add_dist
  have hd0 : 0 ≤ infDist y Γ := infDist_nonneg
  have hd3 : (infDist y Γ)^2 ≤ 9 * ρ^2 := by nlinarith
  constructor <;> linarith [hnd.1, hnd.2]

/-! ## Part B: mass -/

/-! ### One horizontal circle at most near a point -/

/-- Two points of the valleys are at the same height (they lie on one
circle) or they are separated at the scale of the smaller norm:
`dist^2 >= 0.245 min(|p|, |q|)`. -/
theorem lattice_cell_points_separated {p q : LatticeSpace} (hp : p ∈ latticeValleys)
    (hq : q ∈ latticeValleys) :
    q 2 = p 2 ∨ (49/200 : ℝ) * min ‖p‖ ‖q‖ ≤ dist p q ^ 2 := by
  obtain ⟨k1, hk1, i1, j1, hp1⟩ := lattice_local_valley_mem hp
  obtain ⟨k2, hk2, i2, j2, hq2⟩ := lattice_local_valley_mem hq
  rcases lattice_local_circles_separated (le_min hk1 hk2) (min_le_left k1 k2) (min_le_right k1 k2)
      i1 j1 i2 j2 hp1 hq2 with h | h
  · left
    rw [h.2, hp1.2]
  · right
    have hsq := pow_le_pow_left₀ (by positivity) h 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    have hmin : min ‖p‖ ‖q‖ < 2 * (2:ℝ)^(min k1 k2) := by
      rcases le_total k1 k2 with hle | hle
      · rw [min_eq_left hle]
        have h2 : ‖p‖ < (2:ℝ)^(k1+1) := (indexedLatticeCircle_in_shell k1 i1 j1 hp1).2
        rw [pow_succ] at h2
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · rw [min_eq_right hle]
        have h2 : ‖q‖ < (2:ℝ)^(k2+1) := (indexedLatticeCircle_in_shell k2 i2 j2 hq2).2
        rw [pow_succ] at h2
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    norm_num at hsq
    linarith

/-- Two separated valley points cannot both be within `r` of a point `y`
when `r <= sigma(y) / 8`. -/
theorem lattice_cell_sep_scalar {n a b D r : ℝ} (hr : 0 < r) (hry : 64 * r^2 ≤ 1 + n)
    (ha : 16 ≤ a) (hb : 16 ≤ b) (han : n ≤ a + r) (hbn : n ≤ b + r) (hD0 : 0 ≤ D)
    (hD : D < 2 * r) (hsep : (49/200 : ℝ) * min a b ≤ D^2) : False := by
  have hm1 : 16 ≤ min a b := le_min ha hb
  have hm2 : n ≤ min a b + r := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]
      exact han
    · rw [min_eq_right h]
      exact hbn
  have hD2 : D^2 < 4 * r^2 := by nlinarith
  have hr1 : 1 ≤ r := by linarith
  have hr2 : r ≤ r^2 := by nlinarith
  linarith

theorem lattice_cell_coord_le_dist (a b : LatticeSpace) (i : Fin 3) : |a i - b i| ≤ dist a b := by
  have h := PiLp.norm_apply_le (a - b) i
  rw [dist_eq_norm]
  simpa [Real.norm_eq_abs] using h

/-- **Cell lemma.** If `r <= sigma(y) / 8`, then one of the three points
`y`, `y + (r/2) e_3`, `y - (r/2) e_3` is at distance at least `r/2` from the
valleys. -/
theorem lattice_cell_far_point {y : LatticeSpace} {r : ℝ} (hr : 0 < r)
    (hry : 64 * r^2 ≤ 1 + ‖y‖) :
    r/2 ≤ infDist y latticeValleys ∨
    r/2 ≤ infDist (EuclideanSpace.single (2 : Fin 3) (r/2) + y) latticeValleys ∨
    r/2 ≤ infDist (EuclideanSpace.single (2 : Fin 3) (-(r/2)) + y) latticeValleys := by
  by_cases hfar : ∀ q ∈ latticeValleys, r ≤ dist y q
  · left
    rw [le_infDist latticeValleys_nonempty]
    intro q hq
    linarith [hfar q hq]
  · push_neg at hfar
    obtain ⟨p, hp, hpd⟩ := hfar
    have key : ∀ q ∈ latticeValleys, q 2 = p 2 ∨ r ≤ dist y q := by
      intro q hq
      rcases lattice_cell_points_separated hp hq with h | h
      · left
        exact h
      · right
        by_contra hlt
        have hlt' : dist y q < r := not_le.mp hlt
        have t := dist_triangle p y q
        rw [dist_comm p y] at t
        exact lattice_cell_sep_scalar hr hry (lattice_cell_valley_norm_ge hp)
          (lattice_cell_valley_norm_ge hq) (by linarith [(lattice_local_norm_dist y p).1])
          (by linarith [(lattice_local_norm_dist y q).1]) dist_nonneg (by linarith) h
    have shift : ∀ t : ℝ, |t| = r/2 → r/2 ≤ |y 2 + t - p 2| →
        r/2 ≤ infDist (EuclideanSpace.single (2 : Fin 3) t + y) latticeValleys := by
      intro t ht hh
      rw [le_infDist latticeValleys_nonempty]
      intro q hq
      rcases key q hq with h | h
      · have h1 := lattice_cell_coord_le_dist (EuclideanSpace.single (2 : Fin 3) t + y) q 2
        have h2 : (EuclideanSpace.single (2 : Fin 3) t + y) 2 = y 2 + t := by
          simp [add_comm]
        rw [h2, h] at h1
        exact hh.trans h1
      · have t1 := dist_triangle y (EuclideanSpace.single (2 : Fin 3) t + y) q
        have h3 : dist y (EuclideanSpace.single (2 : Fin 3) t + y) = r/2 := by
          rw [dist_eq_norm]
          simp [ht]
        linarith
    by_cases hh : p 2 ≤ y 2
    · right
      left
      apply shift (r/2) (abs_of_pos (by positivity))
      rw [abs_of_nonneg (by linarith)]
      linarith
    · right
      right
      apply shift (-(r/2)) (by rw [abs_neg, abs_of_pos (by positivity)])
      rw [abs_of_nonpos (by linarith)]
      linarith

/-! ### Measure-theoretic steps -/

/-- The weighted measure is at most Lebesgue measure, on every set. -/
theorem lattice_mass_le_volume {α : ℝ} (hα : 0 ≤ α) (s : Set LatticeSpace) :
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) s ≤
      volume s := by
  have h : (volume : Measure LatticeSpace).withDensity
      (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)) ≤ volume.withDensity 1 :=
    withDensity_mono (ae_of_all _ (fun x => by
      simpa using latticeWeight_le_one latticeValleys hα x))
  rw [withDensity_one] at h
  exact Measure.le_iff'.mp h s

theorem lattice_mass_ge_of_weight_ge {α q : ℝ} {s : Set LatticeSpace} (hs : MeasurableSet s)
    (hq : ∀ x ∈ s, q ≤ latticeWeight latticeValleys α x) :
    ENNReal.ofReal q * volume s ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) s := by
  rw [withDensity_apply _ hs, ← setLIntegral_const]
  exact setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hq x hx))

theorem lattice_mass_ball_scale (x y : LatticeSpace) {c : ℝ} (hc : 0 ≤ c) (ρ : ℝ) :
    volume (ball x (c * ρ)) = ENNReal.ofReal (c^3) * volume (ball y ρ) := by
  rw [EuclideanSpace.volume_ball_fin_three, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_mul hc, mul_pow, ENNReal.ofReal_pow hc, mul_assoc]

/-- Three translates of the good set cover a slightly smaller ball. -/
theorem lattice_mass_good_volume {x0 : LatticeSpace} {ρ r : ℝ} (hr : 0 < r)
    (hcell : ∀ y ∈ ball x0 (ρ - r/2), 64 * r^2 ≤ 1 + ‖y‖) :
    volume (ball x0 (ρ - r/2)) ≤
      3 * volume ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) := by
  have hshift : ∀ (t : ℝ) (y : LatticeSpace), |t| = r/2 → y ∈ ball x0 (ρ - r/2) →
      EuclideanSpace.single (2 : Fin 3) t + y ∈ ball x0 ρ := by
    intro t y ht hy
    rw [mem_ball] at hy ⊢
    have t1 := dist_triangle (EuclideanSpace.single (2 : Fin 3) t + y) y x0
    have h3 : dist (EuclideanSpace.single (2 : Fin 3) t + y) y = r/2 := by
      rw [dist_eq_norm]
      simp [ht]
    linarith
  have hsub : ball x0 (ρ - r/2) ⊆
      ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) ∪
      (((fun x : LatticeSpace => EuclideanSpace.single (2 : Fin 3) (r/2) + x) ⁻¹'
        ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ)) ∪
       ((fun x : LatticeSpace => EuclideanSpace.single (2 : Fin 3) (-(r/2)) + x) ⁻¹'
        ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ))) := by
    intro y hy
    rcases lattice_cell_far_point hr (hcell y hy) with h | h | h
    · left
      exact ⟨h, ball_subset_ball (by linarith) hy⟩
    · right
      left
      exact ⟨h, hshift _ y (abs_of_pos (by positivity)) hy⟩
    · right
      right
      exact ⟨h, hshift _ y (by rw [abs_neg, abs_of_pos (by positivity)]) hy⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add_left (measure_union_le _ _) _).trans ?_
  rw [measure_preimage_add, measure_preimage_add]
  apply le_of_eq
  ring

/-- Where `d >= r/2` and `1 + |x| <= A r^2`, the weight is at least
`(4A+1)^(-alpha/2)`. -/
theorem lattice_mass_weight_lower {α : ℝ} (hα : 0 ≤ α) {x : LatticeSpace} {r A : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hd : r/2 ≤ infDist x latticeValleys)
    (hn : 1 + ‖x‖ ≤ A * r^2) :
    (1 / (4*A+1))^(α/2) ≤ latticeWeight latticeValleys α x := by
  have hpos : 0 < 4*A+1 := by positivity
  apply latticeWeight_lower _ hα (by positivity)
  have hd2 : (r/2)^2 ≤ (infDist x latticeValleys)^2 := pow_le_pow_left₀ (by positivity) hd 2
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hd2 hA.le]

/-- Core of the mass bound: a ball with `rho <= |x_0| / 2`, a cell radius
`r <= rho` with `128 r^2 <= sigma_0^2 <= A r^2`. -/
theorem lattice_mass_core {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace} {ρ r A : ℝ} (hr : 0 < r)
    (hrρ : r ≤ ρ) (hρ : 2 * ρ ≤ ‖x0‖) (hlow : 128 * r^2 ≤ 1 + ‖x0‖)
    (hup : 1 + ‖x0‖ ≤ A * r^2) :
    ENNReal.ofReal ((1 / (6*A+1))^(α/2) / 24) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) := by
  have hA : 0 < A := by
    by_contra h
    have h' : A ≤ 0 := not_lt.mp h
    nlinarith [norm_nonneg x0, mul_nonneg (neg_nonneg.mpr h') (sq_nonneg r)]
  have hnorm : ∀ y ∈ ball x0 ρ, ‖x0‖ ≤ 2 * ‖y‖ ∧ 2 * ‖y‖ ≤ 3 * ‖x0‖ := by
    intro y hy
    rw [mem_ball] at hy
    have h := lattice_local_norm_dist y x0
    constructor <;> linarith [h.1, h.2]
  have hGmeas : MeasurableSet
      ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) :=
    (isClosed_le continuous_const (continuous_infDist_pt _)).measurableSet.inter
      measurableSet_ball
  have hgood : volume (ball x0 (ρ - r/2)) ≤
      3 * volume ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) := by
    apply lattice_mass_good_volume hr
    intro y hy
    have h := (hnorm y (ball_subset_ball (by linarith) hy)).1
    linarith
  have hhalf : volume (ball x0 ρ) ≤ 8 * volume (ball x0 (ρ - r/2)) := by
    have h1 := lattice_mass_ball_scale x0 x0 (by norm_num : (0:ℝ) ≤ 2) (ρ/2)
    rw [show 2 * (ρ/2) = ρ by ring, show ENNReal.ofReal ((2:ℝ)^3) = 8 by norm_num] at h1
    rw [h1]
    gcongr
    linarith
  have hw : ∀ x ∈ {x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ,
      (1 / (6*A+1))^(α/2) ≤ latticeWeight latticeValleys α x := by
    intro x hx
    have h := lattice_mass_weight_lower hα hr (by positivity : 0 < 3/2 * A) hx.1
      (by linarith [(hnorm x hx.2).2])
    rwa [show 4 * (3/2 * A) + 1 = 6*A+1 by ring] at h
  have hmass := lattice_mass_ge_of_weight_ge hGmeas hw
  calc ENNReal.ofReal ((1 / (6*A+1))^(α/2) / 24) * volume (ball x0 ρ)
      ≤ ENNReal.ofReal ((1 / (6*A+1))^(α/2) / 24) * (8 * (3 *
          volume ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ))) := by
        gcongr
        exact hhalf.trans (by gcongr)
    _ = ENNReal.ofReal ((1 / (6*A+1))^(α/2)) *
          volume ({x : LatticeSpace | r/2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) := by
        rw [← mul_assoc, ← mul_assoc, mul_assoc (ENNReal.ofReal _),
          show (8:ℝ≥0∞) * 3 = ENNReal.ofReal 24 by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ _ := hmass.trans (measure_mono inter_subset_right)

/-- Mass bound for balls with `rho <= |x_0| / 2` and `rho >= sigma_0 / M`. -/
theorem lattice_mass_ball_lower_far {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M)
    {x0 : LatticeSpace} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : 2 * ρ ≤ ‖x0‖)
    (hσ : 1 + ‖x0‖ ≤ M^2 * ρ^2) :
    ENNReal.ofReal ((1 / (864*M^2+1))^(α/2) / 24) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) := by
  have hσ0 : 0 ≤ 1 + ‖x0‖ := by positivity
  have hsq := Real.sq_sqrt hσ0
  have hM2 : 1 ≤ M^2 := by nlinarith
  rcases le_total ρ (Real.sqrt (1 + ‖x0‖) / 12) with hc | hc
  · have h1 : ρ^2 ≤ (Real.sqrt (1 + ‖x0‖) / 12)^2 := pow_le_pow_left₀ hρ0.le hc 2
    rw [div_pow, hsq] at h1
    have h := lattice_mass_core hα hρ0 le_rfl hρ (by linarith) (A := 144*M^2)
      (by nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg ρ)])
    rwa [show 6 * (144*M^2) + 1 = 864*M^2+1 by ring] at h
  · have h := lattice_mass_core hα (r := Real.sqrt (1 + ‖x0‖) / 12)
      (div_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num)) hc hρ
      (by rw [div_pow, hsq]; linarith) (A := 144*M^2)
      (by rw [div_pow, hsq]; nlinarith [mul_le_mul_of_nonneg_right hM2 hσ0])
    rwa [show 6 * (144*M^2) + 1 = 864*M^2+1 by ring] at h

/-- **Mass bound, all balls of radius at least `sigma_0 / M`.** Squared form
of the hypothesis: `sigma_0^2 <= M^2 rho^2`. -/
theorem lattice_mass_ball_lower {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M) (x0 : LatticeSpace)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hσ : 1 + ‖x0‖ ≤ M^2 * ρ^2) :
    ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) := by
  have hM2 : 1 ≤ M^2 := by nlinarith
  rcases le_or_gt (2 * ρ) ‖x0‖ with hc | hc
  · refine le_trans ?_ (lattice_mass_ball_lower_far hα hM hρ0 hc hσ)
    have h1 : (1 / (21600*M^2+1))^(α/2) ≤ (1 / (864*M^2+1))^(α/2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have h2 : 0 ≤ (1 / (864*M^2+1))^(α/2) := by positivity
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (by linarith)) _
  · obtain ⟨x1, hx1d, hx1n⟩ : ∃ x1 : LatticeSpace, dist x1 x0 = ρ/2 ∧ ρ/2 ≤ ‖x1‖ := by
      have hvn : ‖(EuclideanSpace.single (2 : Fin 3) (ρ/2) : LatticeSpace)‖ = ρ/2 := by
        rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h := norm_sub_le (x0 + EuclideanSpace.single (2 : Fin 3) (ρ/2))
        (x0 - EuclideanSpace.single (2 : Fin 3) (ρ/2))
      have he : (x0 + EuclideanSpace.single (2 : Fin 3) (ρ/2)) -
          (x0 - EuclideanSpace.single (2 : Fin 3) (ρ/2)) =
          (2:ℝ) • (EuclideanSpace.single (2 : Fin 3) (ρ/2) : LatticeSpace) := by
        rw [two_smul]
        abel
      rw [he, norm_smul, hvn, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
      rcases le_total ‖x0 - EuclideanSpace.single (2 : Fin 3) (ρ/2)‖
          ‖x0 + EuclideanSpace.single (2 : Fin 3) (ρ/2)‖ with hh | hh
      · refine ⟨x0 + EuclideanSpace.single (2 : Fin 3) (ρ/2), ?_, by linarith⟩
        rw [dist_eq_norm, add_sub_cancel_left, hvn]
      · refine ⟨x0 - EuclideanSpace.single (2 : Fin 3) (ρ/2), ?_, by linarith⟩
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, hvn]
    have hx1up := (lattice_local_norm_dist x1 x0).1
    have hMρ : 1 ≤ M^2 * ρ := by
      rcases le_total ρ 1 with h1 | h1
      · nlinarith [norm_nonneg x0,
          mul_nonneg (mul_nonneg (sq_nonneg M) hρ0.le) (sub_nonneg.mpr h1)]
      · nlinarith
    have hfar := lattice_mass_ball_lower_far hα (M := 5*M) (by linarith) (x0 := x1)
      (ρ := ρ/4) (by positivity) (by linarith)
      (by nlinarith [mul_le_mul_of_nonneg_right hMρ hρ0.le])
    have hsub : ball x1 (ρ/4) ⊆ ball x0 ρ := ball_subset_ball' (by rw [hx1d]; linarith)
    have hvol := lattice_mass_ball_scale x0 x1 (by norm_num : (0:ℝ) ≤ 4) (ρ/4)
    rw [show 4 * (ρ/4) = ρ by ring] at hvol
    rw [hvol, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine le_trans (le_of_eq ?_) (hfar.trans (measure_mono hsub))
    congr 2
    rw [show 864*(5*M)^2+1 = 21600*M^2+1 by ring]
    ring

/-! ### Items 4 and 5 -/

/-- **Mass of balls, explicit constant.** For `M >= 1` and every ball with
`rho >= sigma(x_0) / M`: `c(M) |B| <= mu(B) <= |B|` with
`c(M) = (21600 M^2 + 1)^(-alpha/2) / 1536`. No upper bound on `rho`. -/
theorem lattice_mass_ball {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M) (x0 : LatticeSpace)
    {ρ : ℝ} (hρ : Real.sqrt (1 + ‖x0‖) / M ≤ ρ) :
    ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) ≤ volume (ball x0 ρ) := by
  refine ⟨?_, lattice_mass_le_volume hα _⟩
  have hM0 : 0 < M := by linarith
  have hσ0 : 0 ≤ 1 + ‖x0‖ := by positivity
  have hs : 0 < Real.sqrt (1 + ‖x0‖) := Real.sqrt_pos.mpr (by positivity)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (div_pos hs hM0) hρ
  rw [div_le_iff₀ hM0] at hρ
  have h := pow_le_pow_left₀ hs.le hρ 2
  rw [Real.sq_sqrt hσ0, mul_pow] at h
  exact lattice_mass_ball_lower hα hM x0 hρ0 (by linarith)

/-- **Cell mass `(eq:cellmass)`, balls.** There is `c > 0` depending only on
`alpha` with `c |B(y,l)| <= mu(B(y,l)) <= |B(y,l)|` whenever
`l >= sigma(y) / 128`. -/
theorem lattice_cell_mass_ball {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (y : LatticeSpace) (l : ℝ), Real.sqrt (1 + ‖y‖) / 128 ≤ l →
      ENNReal.ofReal c * volume (ball y l) ≤
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball y l) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball y l) ≤ volume (ball y l) :=
  ⟨(1 / (21600*(128:ℝ)^2+1))^(α/2) / 1536, by positivity,
    fun y _ hl => lattice_mass_ball hα (by norm_num : (1:ℝ) ≤ 128) y hl⟩

/-- **Large balls.** There is `c > 0` depending only on `alpha` with
`c |B| <= mu(B) <= |B|` for every ball of radius `rho >= sigma(x_0) / 10`. -/
theorem lattice_mass_large_ball {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x0 : LatticeSpace) (ρ : ℝ), Real.sqrt (1 + ‖x0‖) / 10 ≤ ρ →
      ENNReal.ofReal c * volume (ball x0 ρ) ≤
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball x0 ρ) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball x0 ρ) ≤ volume (ball x0 ρ) :=
  ⟨(1 / (21600*(10:ℝ)^2+1))^(α/2) / 1536, by positivity,
    fun x0 _ hρ => lattice_mass_ball hα (by norm_num : (1:ℝ) ≤ 10) x0 hρ⟩

/-- A lower mass bound at a ball gives doubling there, through Lebesgue
measure: `mu(2B) <= |2B| = 8 |B| <= (8/c) mu(B)`. -/
theorem lattice_mass_double_of_lower {α : ℝ} (hα : 0 ≤ α) (x0 : LatticeSpace) {ρ c : ℝ}
    (hc : 0 < c)
    (h : ENNReal.ofReal c * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ)) :
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 (2 * ρ)) ≤
      ENNReal.ofReal (8 / c) *
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball x0 ρ) := by
  refine (lattice_mass_le_volume hα (ball x0 (2 * ρ))).trans ?_
  rw [lattice_mass_ball_scale x0 x0 (by norm_num : (0:ℝ) ≤ 2) ρ]
  calc ENNReal.ofReal ((2:ℝ)^3) * volume (ball x0 ρ)
      = ENNReal.ofReal (8 / c) * (ENNReal.ofReal c * volume (ball x0 ρ)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hc.ne']
        norm_num
    _ ≤ _ := by gcongr

/-- Doubling at every ball of radius at least `sigma(x_0) / M`, with the
explicit constant `8 / c(M)`. -/
theorem lattice_mass_double_ball {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M) (x0 : LatticeSpace)
    {ρ : ℝ} (hρ : Real.sqrt (1 + ‖x0‖) / M ≤ ρ) :
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 (2 * ρ)) ≤
      ENNReal.ofReal (8 / ((1 / (21600*M^2+1))^(α/2) / 1536)) *
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          (ball x0 ρ) :=
  lattice_mass_double_of_lower hα x0 (by positivity) (lattice_mass_ball hα hM x0 hρ).1

/-- Mass of any set squeezed between two concentric balls. -/
theorem lattice_cell_mass_sandwich {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M) (y : LatticeSpace)
    {r K : ℝ} (hK : 0 < K) (hr : Real.sqrt (1 + ‖y‖) / M ≤ r) {Q : Set LatticeSpace}
    (hin : ball y r ⊆ Q) (hout : Q ⊆ ball y (K * r)) :
    ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536 / K^3) * volume Q ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) Q ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) Q ≤
      volume Q := by
  refine ⟨?_, lattice_mass_le_volume hα Q⟩
  have h1 := (lattice_mass_ball hα hM y hr).1
  have h2 : volume Q ≤ ENNReal.ofReal (K^3) * volume (ball y r) := by
    rw [← lattice_mass_ball_scale y y hK.le]
    exact measure_mono hout
  calc ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536 / K^3) * volume Q
      ≤ ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536 / K^3) *
          (ENNReal.ofReal (K^3) * volume (ball y r)) := by gcongr
    _ = ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536) * volume (ball y r) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
    _ ≤ _ := h1.trans (measure_mono hin)

/-- **Cell mass, closed cubes.** The closed cube of side `l` centred at `y`,
with `l / 2 >= sigma(y) / M`. -/
theorem lattice_cell_mass_cube {α : ℝ} (hα : 0 ≤ α) {M : ℝ} (hM : 1 ≤ M) (y : LatticeSpace)
    {l : ℝ} (hl : Real.sqrt (1 + ‖y‖) / M ≤ l / 2) :
    ENNReal.ofReal ((1 / (21600*M^2+1))^(α/2) / 1536 / 8) *
        volume {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ≤
      volume {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} := by
  have hM0 : 0 < M := by linarith
  have hl0 : 0 < l / 2 :=
    lt_of_lt_of_le (div_pos (Real.sqrt_pos.mpr (by positivity)) hM0) hl
  have h := lattice_cell_mass_sandwich hα hM y (K := 2) (by norm_num) hl
    (Q := {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2})
    (by
      intro x hx i
      rw [mem_ball] at hx
      exact (lattice_cell_coord_le_dist x y i).trans hx.le)
    (by
      intro x hx
      rw [mem_ball]
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      have hd := euclidean3_dist_sq x y
      have s0 := sq_le_sq' (neg_le_of_abs_le h0) (le_of_abs_le h0)
      have s1 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
      have s2 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
      by_contra hcon
      have hge : 2 * (l / 2) ≤ dist x y := not_lt.mp hcon
      nlinarith)
  rwa [show (2:ℝ)^3 = 8 by norm_num] at h

/-- **Cell mass `(eq:cellmass)`, cubes.** There is `c > 0` depending only on
`alpha` with `c |Q| <= mu(Q) <= |Q|` for every closed cube `Q` of side
`l >= sigma(y) / 64` centred at `y`. -/
theorem lattice_cell_mass_cube_exists {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (y : LatticeSpace) (l : ℝ), Real.sqrt (1 + ‖y‖) / 64 ≤ l →
      ENNReal.ofReal c * volume {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ≤
        (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ∧
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
          {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} ≤
        volume {x : LatticeSpace | ∀ i, |x i - y i| ≤ l / 2} :=
  ⟨(1 / (21600*(128:ℝ)^2+1))^(α/2) / 1536 / 8, by positivity,
    fun y _ hl => lattice_cell_mass_cube hα (by norm_num : (1:ℝ) ≤ 128) y (by linarith)⟩

/-! ### The paper's own numbers in the cell-mass paragraph -/

/-- Paper: `1 + |x| <= 3 s_k^2` on a cell of size at most `s_k` centred in
shell `k >= 4`. -/
theorem lattice_cell_norm_le {k : ℕ} (hk : 4 ≤ k) {y x : LatticeSpace}
    (h2 : ‖y‖ < (2:ℝ)^(k+1)) (hx : dist x y ≤ Real.sqrt ((2:ℝ)^k)) :
    1 + ‖x‖ ≤ 3 * (2:ℝ)^k := by
  have hS := lattice_local_scale_ge hk
  have hsq : Real.sqrt ((2:ℝ)^k) ^ 2 = (2:ℝ)^k := Real.sq_sqrt (by positivity)
  have hn := (lattice_local_norm_dist x y).1
  rw [pow_succ] at h2
  nlinarith

/-- Paper: where `d >= eps s_k` and `1 + |x| <= 3 s_k^2`, the weight is at
least `(eps^2 / (4 + eps^2))^(alpha/2)`. -/
theorem lattice_cell_weight_lower {α : ℝ} (hα : 0 ≤ α) {k : ℕ} {x : LatticeSpace} {ε : ℝ}
    (hε : 0 < ε) (hd : ε * Real.sqrt ((2:ℝ)^k) ≤ infDist x latticeValleys)
    (hn : 1 + ‖x‖ ≤ 3 * (2:ℝ)^k) :
    (ε^2 / (4 + ε^2))^(α/2) ≤ latticeWeight latticeValleys α x := by
  have hpos : 0 < 4 + ε^2 := by positivity
  apply latticeWeight_lower _ hα (by positivity)
  have hd2 := pow_le_pow_left₀ (by positivity) hd 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hd2
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg ε), sq_nonneg (infDist x latticeValleys),
    sq_nonneg ε]

/-- Paper: "at most `C_0` circles come within `s_k` of `Q` (their meridian
points lie `>= s_k / 2` apart)". The half scale of shell `k` is at most the
radial mesh of every shell `m >= k - 1`. -/
theorem lattice_cell_half_scale_le_mesh {k m : ℕ} (hkm : k ≤ m + 1) :
    Real.sqrt ((2:ℝ)^k) / 2 ≤ (2:ℝ)^m / latticeLayerCount m := by
  have hmesh := lattice_local_mesh_sq_ge m
  have hp : (2:ℝ)^k ≤ (2:ℝ)^(m+1) := pow_le_pow_right₀ (by norm_num) hkm
  rw [pow_succ] at hp
  rw [div_le_iff₀ (by norm_num), Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow]
  nlinarith

/-- The half scale of shell `k` is at most the same-layer spacing
`0.78 L_m` of every shell `m >= k - 1`. -/
theorem lattice_cell_half_scale_le_layer {k m : ℕ} (hkm : k ≤ m + 1) :
    Real.sqrt ((2:ℝ)^k) / 2 ≤ (78/100 : ℝ) * latticeLayerCount m := by
  have hL := lattice_layer_count_ge_sqrt m
  have hp : (2:ℝ)^k ≤ (2:ℝ)^(m+1) := pow_le_pow_right₀ (by norm_num) hkm
  have hs0 : 0 ≤ Real.sqrt ((2:ℝ)^m) := Real.sqrt_nonneg _
  have h1 : Real.sqrt ((2:ℝ)^k) ≤ (3/2 : ℝ) * Real.sqrt ((2:ℝ)^m) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [pow_succ] at hp
    nlinarith [show (0:ℝ) < (2:ℝ)^m by positivity]
  linarith

/-- Circles of two different shells are separated by the radial mesh of the
lower shell (unrounded form of `lattice_distinct_shells_separated`). -/
theorem lattice_cell_distinct_shells_mesh {k k' : ℕ} (hkk : k < k')
    (i : Fin (latticeLayerCount k)) (j : Fin (latticeCirclesPerLayer k))
    (i' : Fin (latticeLayerCount k')) (j' : Fin (latticeCirclesPerLayer k'))
    {x y : LatticeSpace} (hx : x ∈ indexedLatticeCircle k i j)
    (hy : y ∈ indexedLatticeCircle k' i' j') :
    (2:ℝ)^k / latticeLayerCount k ≤ dist x y := by
  have hn := norm_sub_norm_le y x
  rw [← dist_eq_norm, dist_comm, hx.1, hy.1] at hn
  have hup := latticeCircleRadius_upper_gap k i
  have hlo := (latticeCircleRadius_bounds k' i').1
  have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) hkk
  linarith

/-- Paper, cell mass: two distinct circles of shells `>= k - 1` (the circles
that can come near a cell centred in shell `k`) are at least `s_k / 2`
apart. For shell `k - 1` this is sharper than the rounded `0.7 s_(k-1)`. -/
theorem lattice_cell_neighbor_circles_separated {k k1 k2 : ℕ} (hk1 : 4 ≤ k1)
    (h1 : k ≤ k1 + 1) (h2 : k ≤ k2 + 1)
    (i1 : Fin (latticeLayerCount k1)) (j1 : Fin (latticeCirclesPerLayer k1))
    (i2 : Fin (latticeLayerCount k2)) (j2 : Fin (latticeCirclesPerLayer k2))
    {p q : LatticeSpace} (hp : p ∈ indexedLatticeCircle k1 i1 j1)
    (hq : q ∈ indexedLatticeCircle k2 i2 j2) :
    q ∈ indexedLatticeCircle k1 i1 j1 ∨ Real.sqrt ((2:ℝ)^k) / 2 ≤ dist p q := by
  rcases lt_trichotomy k1 k2 with h | h | h
  · right
    exact (lattice_cell_half_scale_le_mesh h1).trans
      (lattice_cell_distinct_shells_mesh h i1 j1 i2 j2 hp hq)
  · subst h
    rcases lt_trichotomy i1.val i2.val with hi | hi | hi
    · right
      exact (lattice_cell_half_scale_le_mesh h1).trans
        (lattice_distinct_layers_separated k1 hi j1 j2 hp hq)
    · have hie : i1 = i2 := Fin.ext hi
      subst hie
      by_cases hj : j1 = j2
      · left
        subst hj
        exact hq
      · right
        exact (lattice_cell_half_scale_le_layer h1).trans
          (lattice_same_layer_separated k1 hk1 i1 hj hp hq)
    · right
      rw [dist_comm]
      exact (lattice_cell_half_scale_le_mesh h1).trans
        (lattice_distinct_layers_separated k1 hi j2 j1 hq hp)
  · right
    rw [dist_comm]
    exact (lattice_cell_half_scale_le_mesh h2).trans
      (lattice_cell_distinct_shells_mesh h i2 j2 i1 j1 hq hp)

/-- A circle that comes within `2 s_k` of a point of norm at least `2^k`,
`k >= 4`, lies in a shell `>= k - 1`. So the circles near a cell centred in
shell `k` are among those of `lattice_cell_neighbor_circles_separated`. -/
theorem lattice_cell_near_circle_shell_ge {k k' : ℕ} (hk : 4 ≤ k)
    (i : Fin (latticeLayerCount k')) (j : Fin (latticeCirclesPerLayer k'))
    {y c : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖y‖) (hc : c ∈ indexedLatticeCircle k' i j)
    (hd : dist y c ≤ 2 * Real.sqrt ((2:ℝ)^k)) : k ≤ k' + 1 := by
  by_contra h
  have hk' : k' + 1 ≤ k - 1 := by omega
  have hp : (2:ℝ)^(k'+1) ≤ (2:ℝ)^(k-1) := pow_le_pow_right₀ (by norm_num) hk'
  have hT : (2:ℝ)^k = 2 * (2:ℝ)^(k-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcn : ‖c‖ < (2:ℝ)^(k'+1) := (indexedLatticeCircle_in_shell k' i j hc).2
  have h3 := (lattice_local_norm_dist y c).1
  have hS := lattice_local_scale_ge hk
  have hsq : Real.sqrt ((2:ℝ)^k) ^ 2 = (2:ℝ)^k := Real.sq_sqrt (by positivity)
  nlinarith

/-! ### Further checks of statements in the two paragraphs -/

/-- Paper: in the near case the nearest circle lies in shell `k` or `k+1`
(upper half; the lower half is `lattice_local_nearest_shell_ge`). -/
theorem lattice_local_nearest_shell_le {k k' : ℕ} (i : Fin (latticeLayerCount k'))
    (j : Fin (latticeCirclesPerLayer k')) {x0 c : LatticeSpace} {ρ : ℝ}
    (h2 : ‖x0‖ < (2:ℝ)^(k+1)) (hρ : ρ ≤ (3/20 : ℝ) * Real.sqrt ((2:ℝ)^k))
    (hc : c ∈ indexedLatticeCircle k' i j) (hcd : dist x0 c ≤ 2 * ρ) : k' ≤ k + 1 := by
  by_contra h
  have hk' : k + 1 + 1 ≤ k' := by omega
  have hp : (2:ℝ)^(k+1+1) ≤ (2:ℝ)^k' := pow_le_pow_right₀ (by norm_num) hk'
  have hcn : (2:ℝ)^k' ≤ ‖c‖ := (indexedLatticeCircle_in_shell k' i j hc).1
  have h3 := (lattice_local_norm_dist x0 c).2
  have hT : (0:ℝ) < (2:ℝ)^k := by positivity
  have hS : Real.sqrt ((2:ℝ)^k) ≤ (2:ℝ)^k := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    nlinarith
  rw [pow_succ] at h2
  rw [pow_succ, pow_succ] at hp
  linarith

/-- Paper, far case: with `tau = dist(x_0, Gamma) >= 2 rho`, the distance
`d` lies in `[tau/2, 3 tau/2]` on `B` and `d <= 2 tau` on `2B`. -/
theorem lattice_local_far_distances {E : Type*} [NormedAddCommGroup E] (Γ : Set E) {x0 : E}
    {ρ : ℝ} (hfar : 2 * ρ ≤ infDist x0 Γ) :
    (∀ y ∈ ball x0 ρ, infDist x0 Γ / 2 ≤ infDist y Γ ∧ infDist y Γ ≤ 3 / 2 * infDist x0 Γ) ∧
    (∀ y ∈ ball x0 (2 * ρ), infDist y Γ ≤ 2 * infDist x0 Γ) := by
  constructor
  · intro y hy
    rw [mem_ball] at hy
    have h1 : infDist y Γ ≤ infDist x0 Γ + dist y x0 := infDist_le_infDist_add_dist
    have h2 : infDist x0 Γ ≤ infDist y Γ + dist x0 y := infDist_le_infDist_add_dist
    rw [dist_comm x0 y] at h2
    constructor <;> linarith
  · intro y hy
    rw [mem_ball] at hy
    have h1 : infDist y Γ ≤ infDist x0 Γ + dist y x0 := infDist_le_infDist_add_dist
    linarith

/-- Paper: a ball of radius at most 8 centred in `{|x| < 16}` lies in
`{|x| <= 32}`, so `33^(-alpha/2) <= w <= 1` on it. -/
theorem lattice_local_small_ball_near_origin {α : ℝ} (hα : 0 ≤ α) {x0 y : LatticeSpace}
    {ρ : ℝ} (hx0 : ‖x0‖ < 16) (hρ : ρ ≤ 8) (hy : y ∈ ball x0 ρ) :
    (1/33 : ℝ)^(α/2) ≤ latticeWeight latticeValleys α y ∧
      latticeWeight latticeValleys α y ≤ 1 := by
  rw [mem_ball] at hy
  have h := (lattice_local_norm_dist y x0).1
  exact lattice_local_near_origin hα (by linarith)

/-- Paper: balls of radius `> 8` centred in `{|x| < 16}` are large balls,
`sigma_0 < 10 rho`. -/
theorem lattice_local_large_radius_near_origin {x0 : LatticeSpace} {ρ : ℝ} (hx0 : ‖x0‖ < 16)
    (hρ : 8 < ρ) : Real.sqrt (1 + ‖x0‖) < 10 * ρ := by
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith [norm_nonneg x0]

/-- The weighted measure is comparable to Lebesgue measure inside
`{|x| <= 32}`. -/
theorem lattice_mass_near_origin {α : ℝ} (hα : 0 ≤ α) {s : Set LatticeSpace}
    (hs : MeasurableSet s) (h32 : ∀ x ∈ s, ‖x‖ ≤ 32) :
    ENNReal.ofReal ((1/33 : ℝ)^(α/2)) * volume s ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) s ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x))) s ≤
      volume s :=
  ⟨lattice_mass_ge_of_weight_ge hs (fun x hx => (lattice_local_near_origin hα (h32 x hx)).1),
    lattice_mass_le_volume hα s⟩

end BrownRadial
