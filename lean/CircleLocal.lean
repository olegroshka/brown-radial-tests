import LebesguePoincare

/-!
`lem:circle` of the paper, first part: the premises of the reduction, the
scales `rho <= a / 6`, the circles of radius at most 16, and the comparison
of masses with the radial weight.

Notation. A horizontal circle is `C = latitudeCircle R theta` with `0 < R`
and `0 < theta < pi`. Its Euclidean radius is `a = R * sin theta` and its
centre is `c = latitudeCenter R theta = (0, 0, R cos theta)`. The paper writes
`R` for what is `a` here.

* `RadialWeightPremise alpha` and `CircleNearPremise alpha` are statements.
  They occur later only as named hypotheses.
* Distance facts (paper, line 825): `| |x - c| - a | <= dist(x, C) <= |x - c| + a`,
  and `dist(x, C) >= |x_3 - c_3|` because the circle lies in a horizontal
  plane. They are proved for any set with these two properties (`circleLike`),
  which covers the circle and the one-point set `{c}` at once; the weight of
  `{c}` is the radial weight.
* Far case (`dist(x_0, C) >= 2 rho`, any radius, any set): the weight varies
  on `B` by a factor at most `9^(alpha/2)` and
  `sup_{2B} w <= 16^(alpha/2) inf_B w`; strong Poincare and doubling at `B`
  with no premise.
* Scales `rho <= a / 6`: doubling and strong Poincare at `B`, from the far
  case and `CircleNearPremise`.
* Circles with `a <= 16`: the weight is comparable to the radial weight with
  the constants `513^(alpha/2)`, so it is doubling and strong Poincare on all
  balls by `RadialWeightPremise`.
* Mass comparison (paper, lines 831--844): for a set `S` between `ball x r`
  and `ball x (K r)` and two `circleLike` sets about the same centre with
  radii at most `A r`, the mass of `S` for one weight is at most a constant
  times the mass of `S` for the other. The lower bound for the mass uses the
  ball of radius `r / 4` about `x` shifted vertically by `r / 2` away from the
  plane of the circle; the paper's tube-volume estimate is not used.
* Doubling at every ball of radius at least `a / 6` (in fact `a / 16`), by
  the paper's route: mass comparison and doubling of the radial weight.
* The doubling half of `RadialWeightPremise` holds outright for
  `alpha >= 0` (`radial_weight_doublingAll`), and so does the doubling half
  of `CircleNearPremise` (`circle_near_doubling`, constant `512 * 16^alpha`,
  any radius). Each premise therefore follows from its Poincare half
  (`radialWeightPremise_of_poincare`, `circleNearPremise_of_poincare`). The
  two premises are nevertheless defined with both halves, as agreed.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### The premises of the reduction -/

/-- Radial weight (Bjorn 2001, Prop. 6 with `k = n = 3`, then the
self-improvement of Hajlasz and Koskela): for every centre `c` the weight
`(1 + |x - c|^2)^(alpha/2)` on three-space is doubling on all balls and
satisfies the strong Poincare inequality on all balls, with constants that do
not depend on `c`. A statement only. -/
def RadialWeightPremise (alpha : ℝ) : Prop :=
  ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧ ∀ c : LatticeSpace,
    doublingAll (volume : Measure LatticeSpace)
        (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2)) D ∧
      ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
        poincareAt (volume : Measure LatticeSpace)
          (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2)) P 1 a r

/-- Near-circle step of `lem:circle` (paper, lines 807--821: Fermi
coordinates, cylinder weight, John domain): for every horizontal circle of
Euclidean radius `a = R sin theta` and every ball `B(x_0, rho)` with
`rho <= a / 6` and `dist(x_0, C) <= 2 rho`, the circle weight is doubling at
that ball and satisfies the strong Poincare inequality at that ball, with
constants that depend on neither the circle nor the ball. A statement only. -/
def CircleNearPremise (alpha : ℝ) : Prop :=
  ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
    ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
      ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
        rho ≤ R * Real.sin theta / 6 →
        Metric.infDist x0 (latitudeCircle R theta) ≤ 2 * rho →
        doublingAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D x0 rho ∧
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) P 1 x0 rho

/-! ### Circles and one-point sets: the two distance properties -/

/-- A nonempty set on the sphere of radius `a` about `c` that lies in the
horizontal plane through `c`. A horizontal circle with its centre and radius
is of this kind, and so is `{c}` with radius zero. -/
def circleLike (Γ : Set LatticeSpace) (c : LatticeSpace) (a : ℝ) : Prop :=
  Γ.Nonempty ∧ (∀ q ∈ Γ, dist q c = a) ∧ ∀ q ∈ Γ, q 2 = c 2

/-- The centre `(0, 0, R cos theta)` of the horizontal circle
`latitudeCircle R theta`. -/
noncomputable def latitudeCenter (R θ : ℝ) : LatticeSpace :=
  EuclideanSpace.single (2 : Fin 3) (R * Real.cos θ)

theorem latitudeCenter_apply_zero (R θ : ℝ) : latitudeCenter R θ 0 = 0 := by
  simp [latitudeCenter]

theorem latitudeCenter_apply_one (R θ : ℝ) : latitudeCenter R θ 1 = 0 := by
  simp [latitudeCenter]

theorem latitudeCenter_apply_two (R θ : ℝ) : latitudeCenter R θ 2 = R * Real.cos θ := by
  simp [latitudeCenter]

/-- Every point of the circle is at distance `a = R sin theta` from the
centre. -/
theorem latitudeCircle_dist_center {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ' : θ < Real.pi)
    {q : LatticeSpace} (hq : q ∈ latitudeCircle R θ) :
    dist q (latitudeCenter R θ) = R * Real.sin θ := by
  have hpos : 0 < R * Real.sin θ := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  have hsq : dist q (latitudeCenter R θ) ^ 2 = (R * Real.sin θ) ^ 2 := by
    rw [euclidean3_dist_sq, latitudeCenter_apply_zero, latitudeCenter_apply_one,
      latitudeCenter_apply_two, hq.2, ← latitudeCircle_horizontal_sq hq]
    ring
  exact (sq_eq_sq₀ dist_nonneg hpos.le).mp hsq

/-- A horizontal circle, with its centre and its Euclidean radius. -/
theorem latitudeCircle_circleLike {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ' : θ < Real.pi) :
    circleLike (latitudeCircle R θ) (latitudeCenter R θ) (R * Real.sin θ) :=
  ⟨latitudeCircle_nonempty hR.le θ, fun _ hq => latitudeCircle_dist_center hR hθ hθ' hq,
    fun q hq => by rw [latitudeCenter_apply_two]; exact hq.2⟩

/-- The one-point set `{c}`, radius zero. -/
theorem circleLike_singleton (c : LatticeSpace) : circleLike {c} c 0 :=
  ⟨singleton_nonempty c, fun q hq => by rw [mem_singleton_iff.mp hq, dist_self],
    fun q hq => by rw [mem_singleton_iff.mp hq]⟩

/-- Every circle of the lattice is a horizontal circle `latitudeCircle R theta`
with `0 < R` and `0 < theta < pi`. -/
theorem indexedLatticeCircle_eq_latitudeCircle (k : ℕ) (i : Fin (latticeLayerCount k))
    (j : Fin (latticeCirclesPerLayer k)) :
    ∃ R θ : ℝ, 0 < R ∧ 0 < θ ∧ θ < Real.pi ∧
      indexedLatticeCircle k i j = latitudeCircle R θ :=
  ⟨latticeCircleRadius k i, latticePolarAngle k (latticeAngleIndex k (i, j)),
    lt_of_lt_of_le (by positivity) (latticeCircleRadius_bounds k i).1,
    (latticePolarAngle_bounds k _).1, (latticePolarAngle_bounds k _).2, rfl⟩

/-- The distance to a horizontal circle is attained; the circle is compact
and nonempty. -/
theorem latitudeCircle_infDist_attained {R θ : ℝ} (hR : 0 ≤ R) (x : LatticeSpace) :
    IsCompact (latitudeCircle R θ) ∧ (latitudeCircle R θ).Nonempty ∧
      ∃ q ∈ latitudeCircle R θ, infDist x (latitudeCircle R θ) = dist x q :=
  ⟨latitudeCircle_isCompact R θ, latitudeCircle_nonempty hR θ,
    (latitudeCircle_isClosed R θ).exists_infDist_eq_dist (latitudeCircle_nonempty hR θ) x⟩

/-- `dist(y, Gamma) <= |y - c| + a`. -/
theorem circleLike_infDist_le {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) (y : LatticeSpace) : infDist y Γ ≤ dist y c + a := by
  obtain ⟨⟨q, hq⟩, hsph, -⟩ := h
  have h1 := infDist_le_dist_of_mem (x := y) hq
  have h2 := dist_triangle y c q
  rw [dist_comm c q, hsph q hq] at h2
  linarith

/-- `| |y - c| - a | <= dist(y, Gamma)`. -/
theorem circleLike_abs_le_infDist {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) (y : LatticeSpace) : |dist y c - a| ≤ infDist y Γ := by
  obtain ⟨hne, hsph, -⟩ := h
  rw [le_infDist hne]
  intro q hq
  have h1 := dist_triangle y q c
  have h2 := dist_triangle q y c
  rw [dist_comm q y] at h2
  rw [hsph q hq] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- The distance to the set is at least the distance to its plane. -/
theorem circleLike_height_le_infDist {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) (y : LatticeSpace) : |y 2 - c 2| ≤ infDist y Γ := by
  obtain ⟨hne, -, hpl⟩ := h
  rw [le_infDist hne]
  intro q hq
  have h1 := lattice_cell_coord_le_dist y q 2
  rwa [hpl q hq] at h1

/-- Paper, line 825, for a horizontal circle with centre `c` and radius
`a = R sin theta`: `| |x - c| - a | <= dist(x, C) <= |x - c| + a`. -/
theorem latitudeCircle_infDist_bounds {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ' : θ < Real.pi)
    (x : LatticeSpace) :
    |‖x - latitudeCenter R θ‖ - R * Real.sin θ| ≤ infDist x (latitudeCircle R θ) ∧
      infDist x (latitudeCircle R θ) ≤ ‖x - latitudeCenter R θ‖ + R * Real.sin θ := by
  rw [← dist_eq_norm]
  exact ⟨circleLike_abs_le_infDist (latitudeCircle_circleLike hR hθ hθ') x,
    circleLike_infDist_le (latitudeCircle_circleLike hR hθ hθ') x⟩

/-- The weight of the one-point set `{c}` is the radial weight about `c`. -/
theorem circleWeight_singleton (c : LatticeSpace) (alpha : ℝ) :
    circleWeight {c} alpha = fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2) := by
  funext x
  rw [circleWeight, infDist_singleton, dist_eq_norm]

/-! ### Scalar comparisons of `(1 + d^2)^(alpha/2)` -/

/-- From `1 + u^2 <= K (1 + t^2)` to the weights. -/
theorem circle_rpow_le_of_base_le {u t K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (h : 1 + u ^ 2 ≤ K * (1 + t ^ 2)) :
    (1 + u ^ 2) ^ β ≤ K ^ β * (1 + t ^ 2) ^ β := by
  rw [← Real.mul_rpow hK (by positivity)]
  exact Real.rpow_le_rpow (by positivity) h hβ

/-- If `u <= L t` with `L >= 1` then `1 + u^2 <= L^2 (1 + t^2)`. -/
theorem circle_base_le_of_le_mul {u t L : ℝ} (hu : 0 ≤ u) (hL : 1 ≤ L) (h : u ≤ L * t) :
    1 + u ^ 2 ≤ L ^ 2 * (1 + t ^ 2) := by
  have h1 : u ^ 2 ≤ (L * t) ^ 2 := pow_le_pow_left₀ hu h 2
  have h2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  rw [mul_pow] at h1
  linarith

/-! ### Far case: `dist(x_0, Gamma) >= 2 rho`, any radius, any set -/

/-- Paper, far case: the weight varies on `B` by a factor at most
`9^(alpha/2)`. -/
theorem circle_far_variation (Γ : Set LatticeSpace) {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    {ρ : ℝ} (hfar : 2 * ρ ≤ infDist x0 Γ) {y z : LatticeSpace} (hy : y ∈ ball x0 ρ)
    (hz : z ∈ ball x0 ρ) : circleWeight Γ α y ≤ (9 : ℝ) ^ (α / 2) * circleWeight Γ α z := by
  have hd := (lattice_local_far_distances Γ hfar).1
  have hy' := hd y hy
  have hz' := hd z hz
  have h0 : 0 ≤ infDist y Γ := infDist_nonneg
  refine circle_rpow_le_of_base_le (by norm_num) (by positivity) ?_
  have h3 : infDist y Γ ≤ 3 * infDist z Γ := by linarith [hy'.2, hz'.1]
  have h := circle_base_le_of_le_mul h0 (by norm_num : (1 : ℝ) ≤ 3) h3
  norm_num at h
  exact h

/-- Paper, far case: `sup_{2B} w <= 16^(alpha/2) inf_B w`. -/
theorem circle_far_sup_le_inf (Γ : Set LatticeSpace) {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    {ρ : ℝ} (hfar : 2 * ρ ≤ infDist x0 Γ) {y z : LatticeSpace} (hy : y ∈ ball x0 (2 * ρ))
    (hz : z ∈ ball x0 ρ) : circleWeight Γ α y ≤ (16 : ℝ) ^ (α / 2) * circleWeight Γ α z := by
  have hd := lattice_local_far_distances Γ hfar
  have hy' := hd.2 y hy
  have hz' := hd.1 z hz
  have h0 : 0 ≤ infDist y Γ := infDist_nonneg
  refine circle_rpow_le_of_base_le (by norm_num) (by positivity) ?_
  have h3 : infDist y Γ ≤ 4 * infDist z Γ := by linarith [hz'.1]
  have h := circle_base_le_of_le_mul h0 (by norm_num : (1 : ℝ) ≤ 4) h3
  norm_num at h
  exact h

/-- Far case: strong Poincare at `B` with constant `32 * 9^(alpha/2)`. No
premise, no restriction on the radius. -/
theorem circle_far_poincare (Γ : Set LatticeSpace) {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    {ρ : ℝ} (hρ0 : 0 < ρ) (hfar : 2 * ρ ≤ infDist x0 Γ) :
    poincareAt (volume : Measure LatticeSpace) (circleWeight Γ α)
      (ENNReal.ofReal ((9 : ℝ) ^ (α / 2)) * 32) 1 x0 ρ := by
  obtain ⟨m, hm, hlo, hhi⟩ := lattice_small_inf_pivot (w := circleWeight Γ α)
    (circleWeight_pos Γ α) (S := ball x0 ρ) (T := ball x0 ρ)
    (by positivity : (0 : ℝ) < (9 : ℝ) ^ (α / 2)) (mem_ball_self hρ0) (mem_ball_self hρ0)
    (fun y hy z hz => circle_far_variation Γ hα hfar hy hz)
  have h := poincareAt_of_bounds_three hm (fun x hx => ⟨hlo x hx, hhi x hx⟩)
  rwa [mul_div_cancel_right₀ _ hm.ne'] at h

/-- Far case: doubling at `B` with constant `8 * 16^(alpha/2)`. -/
theorem circle_far_doubling (Γ : Set LatticeSpace) {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    {ρ : ℝ} (hρ0 : 0 < ρ) (hfar : 2 * ρ ≤ infDist x0 Γ) :
    doublingAt (volume : Measure LatticeSpace) (circleWeight Γ α)
      (ENNReal.ofReal ((16 : ℝ) ^ (α / 2)) * 8) x0 ρ := by
  obtain ⟨m, hm, hlo, hhi⟩ := lattice_small_inf_pivot (w := circleWeight Γ α)
    (circleWeight_pos Γ α) (S := ball x0 (2 * ρ)) (T := ball x0 ρ)
    (by positivity : (0 : ℝ) < (16 : ℝ) ^ (α / 2)) (mem_ball_self (by linarith))
    (mem_ball_self hρ0) (fun y hy z hz => circle_far_sup_le_inf Γ hα hfar hy hz)
  have h := doublingAt_of_bounds_three hm hhi hlo
  rwa [mul_div_cancel_right₀ _ hm.ne'] at h

/-! ### Scales `rho <= a / 6` -/

/-- **Scales `rho <= a / 6`** (paper, first part of the proof of
`lem:circle`). Doubling and the strong Poincare inequality at every ball
`B(x_0, rho)` with `rho <= a / 6`, `a = R sin theta`, with constants that
depend only on `alpha`: the far case if `dist(x_0, C) >= 2 rho`, and
`CircleNearPremise` otherwise. -/
theorem circle_small_ball {alpha : ℝ} (halpha : 0 ≤ alpha) (hnear : CircleNearPremise alpha) :
    ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho → rho ≤ R * Real.sin theta / 6 →
          doublingAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) D x0 rho ∧
            poincareAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) P 1 x0 rho := by
  obtain ⟨Dn, Pn, hDn, hPn, hn⟩ := hnear
  refine ⟨max Dn (ENNReal.ofReal ((16 : ℝ) ^ (alpha / 2)) * 8),
    max Pn (ENNReal.ofReal ((9 : ℝ) ^ (alpha / 2)) * 32),
    (max_lt hDn.lt_top (by finiteness)).ne, (max_lt hPn.lt_top (by finiteness)).ne, ?_⟩
  intro R theta hR hθ hθ' x0 rho hρ0 hρ
  rcases le_total (infDist x0 (latitudeCircle R theta)) (2 * rho) with h | h
  · obtain ⟨hd, hp⟩ := hn R theta hR hθ hθ' x0 rho hρ0 hρ h
    exact ⟨doublingAt_mono (le_max_left _ _) hd, poincareAt_mono (le_max_left _ _) hp⟩
  · exact ⟨doublingAt_mono (le_max_right _ _) (circle_far_doubling _ halpha hρ0 h),
      poincareAt_mono (le_max_right _ _) (circle_far_poincare _ halpha hρ0 h)⟩

/-! ### Circles of radius at most 16 -/

/-- Paper: if `a <= 16` then `1 + dist(x, C)^2` and `1 + |x - c|^2` are
comparable with absolute constants. Here the constant is `513`, on both
sides, and the weights are compared with `513^(alpha/2)`. -/
theorem circleLike_weight_compare_radial {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) (ha : a ≤ 16) {α : ℝ} (hα : 0 ≤ α) (x : LatticeSpace) :
    ((513 : ℝ) ^ (α / 2))⁻¹ * (1 + ‖x - c‖ ^ 2) ^ (α / 2) ≤ circleWeight Γ α x ∧
      circleWeight Γ α x ≤ (513 : ℝ) ^ (α / 2) * (1 + ‖x - c‖ ^ 2) ^ (α / 2) := by
  have h1 := circleLike_infDist_le h x
  have h2 := (abs_le.mp (circleLike_abs_le_infDist h x)).2
  have hd0 : 0 ≤ infDist x Γ := infDist_nonneg
  have ht0 : 0 ≤ dist x c := dist_nonneg
  rw [← dist_eq_norm]
  have hup : 1 + infDist x Γ ^ 2 ≤ 513 * (1 + dist x c ^ 2) := by
    have h3 : infDist x Γ ^ 2 ≤ (dist x c + 16) ^ 2 := pow_le_pow_left₀ hd0 (by linarith) 2
    nlinarith [sq_nonneg (dist x c - 16)]
  have hlo : 1 + dist x c ^ 2 ≤ 513 * (1 + infDist x Γ ^ 2) := by
    have h3 : dist x c ^ 2 ≤ (infDist x Γ + 16) ^ 2 := pow_le_pow_left₀ ht0 (by linarith) 2
    nlinarith [sq_nonneg (infDist x Γ - 16)]
  have hβ : 0 ≤ α / 2 := by positivity
  refine ⟨?_, circle_rpow_le_of_base_le (by norm_num) hβ hup⟩
  rw [inv_mul_le_iff₀ (by positivity)]
  exact circle_rpow_le_of_base_le (by norm_num) hβ hlo

/-- **Circles with `a <= 16`** (paper, second part, first case). The circle
weight is doubling and satisfies the strong Poincare inequality on all balls,
by comparison with the radial weight about the centre and
`RadialWeightPremise`. One pair of constants for all such circles. -/
theorem circle_small_radius_all_balls {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) :
    ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi → R * Real.sin theta ≤ 16 →
        doublingAll (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D ∧
          ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
            poincareAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) P 1 a r := by
  obtain ⟨Dr, Pr, hDr, hPr, hr⟩ := hradial
  have hc : (0 : ℝ) < ((513 : ℝ) ^ (alpha / 2))⁻¹ := by positivity
  have hC : (0 : ℝ) ≤ (513 : ℝ) ^ (alpha / 2) := by positivity
  refine ⟨ENNReal.ofReal ((513 : ℝ) ^ (alpha / 2)) * Dr /
      ENNReal.ofReal (((513 : ℝ) ^ (alpha / 2))⁻¹),
    ENNReal.ofReal ((513 : ℝ) ^ (alpha / 2)) * Pr /
      ENNReal.ofReal (((513 : ℝ) ^ (alpha / 2))⁻¹),
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDr)
      (ENNReal.ofReal_pos.mpr hc).ne',
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPr)
      (ENNReal.ofReal_pos.mpr hc).ne', ?_⟩
  intro R theta hR hθ hθ' ha
  have hlike := latitudeCircle_circleLike hR hθ hθ'
  obtain ⟨hd, hp⟩ := hr (latitudeCenter R theta)
  refine ⟨fun a r hr0 => ?_, fun a r hr0 => ?_⟩
  · exact doublingAt_transfer_local_real hc hC
      (fun x _ => circleLike_weight_compare_radial hlike ha halpha x) (hd a r hr0)
  · exact poincareAt_transfer_local_real hc hC le_rfl
      (fun x _ => circleLike_weight_compare_radial hlike ha halpha x) (hp a r hr0)

/-! ### Mass comparison -/

/-- A point at distance `r / 2` from `x`, at height at least `r / 2` above or
below the horizontal plane through `c`, and at least as far from `c` as `x`
is: `x` shifted vertically away from that plane. -/
theorem circle_shift_point (x c : LatticeSpace) {r : ℝ} (hr : 0 < r) :
    ∃ x1 : LatticeSpace, dist x1 x = r / 2 ∧ r / 2 ≤ |x1 2 - c 2| ∧ dist x c ≤ dist x1 c := by
  have key : ∀ t : ℝ, |t| = r / 2 → 0 ≤ t * (x 2 - c 2) →
      dist (EuclideanSpace.single (2 : Fin 3) t + x) x = r / 2 ∧
      r / 2 ≤ |(EuclideanSpace.single (2 : Fin 3) t + x) 2 - c 2| ∧
      dist x c ≤ dist (EuclideanSpace.single (2 : Fin 3) t + x) c := by
    intro t ht hsign
    have e2 : (EuclideanSpace.single (2 : Fin 3) t + x) 2 = x 2 + t := by simp [add_comm]
    have e0 : (EuclideanSpace.single (2 : Fin 3) t + x) 0 = x 0 := by simp
    have e1 : (EuclideanSpace.single (2 : Fin 3) t + x) 1 = x 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [dist_eq_norm]
      simp [ht]
    · rw [e2, ← ht]
      exact sq_le_sq.mp (by nlinarith)
    · refine (sq_le_sq₀ dist_nonneg dist_nonneg).mp ?_
      rw [euclidean3_dist_sq, euclidean3_dist_sq, e0, e1, e2]
      nlinarith
  rcases le_total (c 2) (x 2) with hc | hc
  · exact ⟨_, key (r / 2) (abs_of_pos (by positivity))
      (mul_nonneg (by positivity) (by linarith))⟩
  · exact ⟨_, key (-(r / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
      (by nlinarith)⟩

/-- On the ball of radius `r / 4` about the shifted point, the distance to a
`circleLike` set of radius at most `A r` is at least `(|x - c| + r) / (6 + 4 A)`. -/
theorem circle_shift_infDist_ge {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) {x x1 : LatticeSpace} {r A : ℝ} (hA : 0 ≤ A)
    (ha : a ≤ A * r) (h1 : r / 2 ≤ |x1 2 - c 2|) (h2 : dist x c ≤ dist x1 c)
    {y : LatticeSpace} (hy : y ∈ ball x1 (r / 4)) :
    dist x c + r ≤ (6 + 4 * A) * infDist y Γ := by
  rw [mem_ball] at hy
  have hh := circleLike_height_le_infDist h y
  have habs := (abs_le.mp (circleLike_abs_le_infDist h y)).2
  have hc := lattice_cell_coord_le_dist x1 y 2
  have htri := abs_sub_le (x1 2) (y 2) (c 2)
  have hd := dist_triangle x1 y c
  rw [dist_comm x1 y] at hc hd
  have hd4 : r / 4 ≤ infDist y Γ := by linarith
  have h5 : (5 + 4 * A) * (r / 4) ≤ (5 + 4 * A) * infDist y Γ :=
    mul_le_mul_of_nonneg_left hd4 (by linarith)
  nlinarith

/-- On `ball x (K r)` the distance to a `circleLike` set of radius at most
`A r` is at most `(K + A) (|x - c| + r)` (paper: `dist(y, C) <= D + 17 rho'`). -/
theorem circle_ball_infDist_le {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) {x : LatticeSpace} {r A K : ℝ} (hA : 0 ≤ A)
    (hK : 1 ≤ K) (ha : a ≤ A * r) {z : LatticeSpace} (hz : z ∈ ball x (K * r)) :
    infDist z Γ ≤ (K + A) * (dist x c + r) := by
  rw [mem_ball] at hz
  have h1 := circleLike_infDist_le h z
  have h2 := dist_triangle z x c
  have h3 : 0 ≤ (K + A - 1) * dist x c := mul_nonneg (by linarith) dist_nonneg
  nlinarith

/-- Paper, line 837, as written: on `B' = B(x, rho')` with `a <= 16 rho'`,
`dist(y, C) <= |y - c| + a <= D + 17 rho'`, where `D = |x - c|`. -/
theorem circle_paper_upper_distance {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) {x : LatticeSpace} {rho : ℝ} (ha : a ≤ 16 * rho)
    {y : LatticeSpace} (hy : y ∈ ball x rho) : infDist y Γ ≤ dist x c + 17 * rho := by
  rw [mem_ball] at hy
  have h1 := circleLike_infDist_le h y
  have h2 := dist_triangle y x c
  linarith

/-- Paper, line 838, as written: if `D >= 34 rho'` then
`dist(y, C) >= D - rho' - a >= D / 2` on `B'`. -/
theorem circle_paper_far_lower_distance {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) {x : LatticeSpace} {rho : ℝ} (ha : a ≤ 16 * rho)
    (hD : 34 * rho ≤ dist x c) {y : LatticeSpace} (hy : y ∈ ball x rho) :
    dist x c / 2 ≤ infDist y Γ := by
  rw [mem_ball] at hy
  have h1 := (abs_le.mp (circleLike_abs_le_infDist h y)).2
  have h2 := dist_triangle x y c
  rw [dist_comm x y] at h2
  linarith

/-- The constant of the mass comparison: `((K + A)(6 + 4A))^alpha (4K)^3`. -/
noncomputable def circleMassConst (K A α : ℝ) : ℝ :=
  (((K + A) * (6 + 4 * A)) ^ 2) ^ (α / 2) * (4 * K) ^ 3

theorem circleMassConst_nonneg (K A α : ℝ) (hK : 0 ≤ K) : 0 ≤ circleMassConst K A α := by
  unfold circleMassConst
  positivity

/-- Measure step of the mass comparison. If `f <= M` on `B(x, K r)`, `g >= m`
on a ball of radius `r / 4` inside `B(x, r)`, and `M <= L m`, then the mass of
`B(x, K r)` for `f` is at most `L (4K)^3` times the mass of `B(x, r)` for
`g`. -/
theorem circle_mass_le_of_bounds {f g : LatticeSpace → ℝ} {x x1 : LatticeSpace}
    {r K M m L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hB1 : ball x1 (r / 4) ⊆ ball x r)
    (hup : ∀ z ∈ ball x (K * r), f z ≤ M) (hlow : ∀ y ∈ ball x1 (r / 4), m ≤ g y)
    (hMm : M ≤ L * m) :
    (volume.withDensity fun y => ENNReal.ofReal (f y)) (ball x (K * r)) ≤
      ENNReal.ofReal (L * (4 * K) ^ 3) *
        (volume.withDensity fun y => ENNReal.ofReal (g y)) (ball x r) := by
  have hvol : volume (ball x (K * r)) =
      ENNReal.ofReal ((4 * K) ^ 3) * volume (ball x1 (r / 4)) := by
    have h := lattice_mass_ball_scale x x1 (c := 4 * K) (by linarith) (r / 4)
    rwa [show 4 * K * (r / 4) = K * r by ring] at h
  have h1 : (volume.withDensity fun y => ENNReal.ofReal (f y)) (ball x (K * r)) ≤
      ENNReal.ofReal M * volume (ball x (K * r)) := by
    rw [withDensity_apply _ measurableSet_ball, ← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball
      (fun z hz => ENNReal.ofReal_le_ofReal (hup z hz))
  have h2 : ENNReal.ofReal m * volume (ball x1 (r / 4)) ≤
      (volume.withDensity fun y => ENNReal.ofReal (g y)) (ball x r) := by
    refine le_trans ?_ (measure_mono hB1)
    rw [withDensity_apply _ measurableSet_ball, ← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball
      (fun z hz => ENNReal.ofReal_le_ofReal (hlow z hz))
  calc (volume.withDensity fun y => ENNReal.ofReal (f y)) (ball x (K * r))
      ≤ ENNReal.ofReal M * volume (ball x (K * r)) := h1
    _ ≤ ENNReal.ofReal (L * m) * (ENNReal.ofReal ((4 * K) ^ 3) * volume (ball x1 (r / 4))) := by
        rw [hvol]
        exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hMm) _
    _ = ENNReal.ofReal (L * (4 * K) ^ 3) * (ENNReal.ofReal m * volume (ball x1 (r / 4))) := by
        rw [ENNReal.ofReal_mul hL, ENNReal.ofReal_mul hL]
        ring
    _ ≤ _ := mul_le_mul_left' h2 _

/-- **Mass comparison, core.** Two `circleLike` sets about the same centre
with radii at most `A r`, and any ball `B(x, r)`: the mass of `B(x, K r)` for
the weight of the first set is at most a constant times the mass of `B(x, r)`
for the weight of the second. The constant depends only on `K`, `A` and
`alpha`. No lower bound on `r` and no condition on the position of `x`. -/
theorem circle_mass_ball_le {Γ Γ' : Set LatticeSpace} {c : LatticeSpace} {a a' : ℝ}
    (hΓ : circleLike Γ c a) (hΓ' : circleLike Γ' c a') {α : ℝ} (hα : 0 ≤ α)
    (x : LatticeSpace) {r A K : ℝ} (hr : 0 < r) (hA : 0 ≤ A) (hK : 1 ≤ K) (ha : a ≤ A * r)
    (ha' : a' ≤ A * r) :
    (volume.withDensity fun y => ENNReal.ofReal (circleWeight Γ α y)) (ball x (K * r)) ≤
      ENNReal.ofReal (circleMassConst K A α) *
        (volume.withDensity fun y => ENNReal.ofReal (circleWeight Γ' α y)) (ball x r) := by
  obtain ⟨x1, hx1, hh, hD⟩ := circle_shift_point x c hr
  have hT0 : 0 < dist x c + r := by positivity
  have hKA : 1 ≤ K + A := by linarith
  have h64 : 0 < 6 + 4 * A := by linarith
  have hβ : 0 ≤ α / 2 := by positivity
  have hup : ∀ z ∈ ball x (K * r),
      circleWeight Γ α z ≤ (1 + ((K + A) * (dist x c + r)) ^ 2) ^ (α / 2) := by
    intro z hz
    have h1 := circle_ball_infDist_le hΓ hA hK ha hz
    have h2 := pow_le_pow_left₀ (infDist_nonneg (x := z) (s := Γ)) h1 2
    unfold circleWeight
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ
  have hlow : ∀ y ∈ ball x1 (r / 4),
      (1 + ((dist x c + r) / (6 + 4 * A)) ^ 2) ^ (α / 2) ≤ circleWeight Γ' α y := by
    intro y hy
    have h1 := circle_shift_infDist_ge hΓ' hA ha' hh hD hy
    have h2 : (dist x c + r) / (6 + 4 * A) ≤ infDist y Γ' := by
      rw [div_le_iff₀ h64]
      linarith
    have h3 := pow_le_pow_left₀ (by positivity) h2 2
    unfold circleWeight
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ
  have hMm : (1 + ((K + A) * (dist x c + r)) ^ 2) ^ (α / 2) ≤
      (((K + A) * (6 + 4 * A)) ^ 2) ^ (α / 2) *
        (1 + ((dist x c + r) / (6 + 4 * A)) ^ 2) ^ (α / 2) := by
    refine circle_rpow_le_of_base_le (by positivity) hβ ?_
    refine circle_base_le_of_le_mul (by positivity) (by nlinarith) (le_of_eq ?_)
    field_simp
  have hB1 : ball x1 (r / 4) ⊆ ball x r := ball_subset_ball' (by rw [hx1]; linarith)
  unfold circleMassConst
  exact circle_mass_le_of_bounds (by linarith) (by positivity) hB1 hup hlow hMm

theorem circleWeight_singleton_apply (c : LatticeSpace) (alpha : ℝ) (x : LatticeSpace) :
    circleWeight {c} alpha x = (1 + ‖x - c‖ ^ 2) ^ (alpha / 2) := by
  rw [circleWeight_singleton]

/-- **Mass comparison for balls** (paper, lines 831--844): for every ball
`B' = B(x, rho')` with `rho' >= a / 16`, the masses of `B'` for the circle
weight and for the radial weight about the centre of the circle are
comparable, with a constant that depends only on `alpha`. No lower bound on
`a` is used. -/
theorem circle_mass_ball_comparable {R theta : ℝ} (hR : 0 < R) (hθ : 0 < theta)
    (hθ' : theta < Real.pi) {alpha : ℝ} (halpha : 0 ≤ alpha) (x : LatticeSpace) {rho : ℝ}
    (hrho : R * Real.sin theta / 16 ≤ rho) :
    (volume.withDensity fun y =>
        ENNReal.ofReal (circleWeight (latitudeCircle R theta) alpha y)) (ball x rho) ≤
      ENNReal.ofReal (circleMassConst 1 16 alpha) *
        (volume.withDensity fun y =>
          ENNReal.ofReal ((1 + ‖y - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2))) (ball x rho) ∧
    (volume.withDensity fun y =>
        ENNReal.ofReal ((1 + ‖y - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2))) (ball x rho) ≤
      ENNReal.ofReal (circleMassConst 1 16 alpha) *
        (volume.withDensity fun y =>
          ENNReal.ofReal (circleWeight (latitudeCircle R theta) alpha y)) (ball x rho) := by
  have hlike := latitudeCircle_circleLike hR hθ hθ'
  have hsing := circleLike_singleton (latitudeCenter R theta)
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  have hpos : 0 < rho := by linarith
  have ha : R * Real.sin theta ≤ 16 * rho := by linarith
  have h0 : (0 : ℝ) ≤ 16 * rho := by linarith
  have h1 := circle_mass_ball_le hlike hsing halpha x hpos (A := 16) (K := 1) (by norm_num)
    le_rfl ha h0
  have h2 := circle_mass_ball_le hsing hlike halpha x hpos (A := 16) (K := 1) (by norm_num)
    le_rfl h0 ha
  rw [one_mul] at h1 h2
  simp only [circleWeight_singleton_apply] at h1 h2
  exact ⟨h1, h2⟩

/-- A cube of side `h` lies in the open ball of radius `h` about its centre. -/
theorem circle_cube_subset_ball (y : LatticeSpace) {h : ℝ} (hh : 0 < h) :
    cube y h ⊆ ball y h := by
  intro z hz
  have hd := lattice_covering_cube_dist hh.le hz
  rw [mem_ball]
  linarith

/-- **Mass comparison for cubes** (the form (G1) of `lem:glue`): for every
closed cube `Q` of side `h >= a / 16`, wherever its centre, the masses of `Q`
for the circle weight and for the radial weight are comparable, with a
constant that depends only on `alpha`. Proved directly from the core, with
the ball of radius `h / 2` inside the cube and the ball of radius `h` around
it; the paper passes through doubling at the scale `a / 32`. -/
theorem circle_mass_cube_comparable {R theta : ℝ} (hR : 0 < R) (hθ : 0 < theta)
    (hθ' : theta < Real.pi) {alpha : ℝ} (halpha : 0 ≤ alpha) (y : LatticeSpace) {h : ℝ}
    (hh : R * Real.sin theta / 16 ≤ h) :
    (volume.withDensity fun z =>
        ENNReal.ofReal (circleWeight (latitudeCircle R theta) alpha z)) (cube y h) ≤
      ENNReal.ofReal (circleMassConst 2 32 alpha) *
        (volume.withDensity fun z =>
          ENNReal.ofReal ((1 + ‖z - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2))) (cube y h) ∧
    (volume.withDensity fun z =>
        ENNReal.ofReal ((1 + ‖z - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2))) (cube y h) ≤
      ENNReal.ofReal (circleMassConst 2 32 alpha) *
        (volume.withDensity fun z =>
          ENNReal.ofReal (circleWeight (latitudeCircle R theta) alpha z)) (cube y h) := by
  have hlike := latitudeCircle_circleLike hR hθ hθ'
  have hsing := circleLike_singleton (latitudeCenter R theta)
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  have hpos : 0 < h := by linarith
  have ha : R * Real.sin theta ≤ 32 * (h / 2) := by linarith
  have h0 : (0 : ℝ) ≤ 32 * (h / 2) := by linarith
  have hout : cube y h ⊆ ball y (2 * (h / 2)) := by
    rw [show 2 * (h / 2) = h by ring]
    exact circle_cube_subset_ball y hpos
  have hin : ball y (h / 2) ⊆ cube y h :=
    ball_subset_closedBall.trans (cube_closedBall_subset y h)
  have h1 := circle_mass_ball_le hlike hsing halpha y (r := h / 2) (by linarith) (A := 32)
    (K := 2) (by norm_num) (by norm_num) ha h0
  have h2 := circle_mass_ball_le hsing hlike halpha y (r := h / 2) (by linarith) (A := 32)
    (K := 2) (by norm_num) (by norm_num) h0 ha
  simp only [circleWeight_singleton_apply] at h1 h2
  exact ⟨(measure_mono hout).trans (h1.trans (mul_le_mul_left' (measure_mono hin) _)),
    (measure_mono hout).trans (h2.trans (mul_le_mul_left' (measure_mono hin) _))⟩

/-! ### Doubling at balls of radius at least `a / 16` -/

/-- **Doubling above the scale `a / 16`**, by the paper's route:
`mu(2B) <~ nu(2B) <~ nu(B) <~ mu(B)`, from the mass comparison and doubling
of the radial weight. The range `rho >= a / 16` contains `rho >= a / 6`. -/
theorem circle_large_ball_doubling {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (x0 : LatticeSpace) (rho : ℝ), R * Real.sin theta / 16 ≤ rho →
          doublingAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D x0 rho := by
  obtain ⟨Dr, Pr, hDr, -, hr⟩ := hradial
  refine ⟨ENNReal.ofReal (circleMassConst 1 16 alpha) *
      (Dr * ENNReal.ofReal (circleMassConst 1 16 alpha)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hDr ENNReal.ofReal_ne_top), ?_⟩
  intro R theta hR hθ hθ' x0 rho hrho
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  have hpos : 0 < rho := by linarith
  have h1 := (circle_mass_ball_comparable hR hθ hθ' halpha x0 (rho := 2 * rho)
    (by linarith)).1
  have h2 : doublingAt (volume : Measure LatticeSpace)
      (fun x => (1 + ‖x - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2)) Dr x0 rho :=
    (hr (latitudeCenter R theta)).1 x0 rho hpos
  have h3 := (circle_mass_ball_comparable hR hθ hθ' halpha x0 hrho).2
  unfold doublingAt at h2 ⊢
  refine (h1.trans (mul_le_mul_left' (h2.trans (mul_le_mul_left' h3 _)) _)).trans
    (le_of_eq ?_)
  simp only [mul_assoc]

/-- Doubling above the scale `a / 16` with no premise: the core mass bound
with the same weight on both sides. Not the paper's route; it shows that
doubling of the radial weight is not needed for this step. -/
theorem circle_large_ball_doubling_direct {R theta : ℝ} (hR : 0 < R) (hθ : 0 < theta)
    (hθ' : theta < Real.pi) {alpha : ℝ} (halpha : 0 ≤ alpha) (x0 : LatticeSpace) {rho : ℝ}
    (hrho : R * Real.sin theta / 16 ≤ rho) :
    doublingAt (volume : Measure LatticeSpace) (circleWeight (latitudeCircle R theta) alpha)
      (ENNReal.ofReal (circleMassConst 2 16 alpha)) x0 rho := by
  have hlike := latitudeCircle_circleLike hR hθ hθ'
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  exact circle_mass_ball_le hlike hlike halpha x0 (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by linarith)

/-! ### The doubling half of `RadialWeightPremise` holds outright -/

/-- For `alpha >= 0` the radial weight `(1 + |x - c|^2)^(alpha/2)` is doubling
on all balls with the constant `512 * 144^(alpha/2)`, for every centre. -/
theorem radial_weight_doublingAll {alpha : ℝ} (halpha : 0 ≤ alpha) (c : LatticeSpace) :
    doublingAll (volume : Measure LatticeSpace) (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2))
      (ENNReal.ofReal (circleMassConst 2 0 alpha)) := by
  intro a r hr
  have h := circle_mass_ball_le (circleLike_singleton c) (circleLike_singleton c) halpha a hr
    (A := 0) (K := 2) le_rfl (by norm_num) (by simp) (by simp)
  simp only [circleWeight_singleton_apply] at h
  exact h

/-- `RadialWeightPremise alpha` follows, for `alpha >= 0`, from its Poincare
half alone. -/
theorem radialWeightPremise_of_poincare {alpha : ℝ} (halpha : 0 ≤ alpha)
    (h : ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (c a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace)
        (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2)) P 1 a r) :
    RadialWeightPremise alpha := by
  obtain ⟨P, hP, hp⟩ := h
  exact ⟨ENNReal.ofReal (circleMassConst 2 0 alpha), P, ENNReal.ofReal_ne_top, hP,
    fun c => ⟨radial_weight_doublingAll halpha c, fun a r hr => hp c a r hr⟩⟩

/-! ### The doubling half of `CircleNearPremise` holds outright -/

/-- **Near case, doubling, with no premise.** For a set in a horizontal
plane, `alpha >= 0` and a ball `B(x_0, rho)` with `dist(x_0, Gamma) <= 2 rho`,
of any radius: `mu(2B) <= 512 * 16^alpha * mu(B)`. On `2B` the distance to the
set is at most `4 rho`; on the ball of radius `rho / 4` about `x_0` shifted
vertically by `rho / 2` away from the plane it is at least `rho / 4`. -/
theorem circle_near_doubling {Γ : Set LatticeSpace} {c : LatticeSpace} {a : ℝ}
    (h : circleLike Γ c a) {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace} {ρ : ℝ} (hρ : 0 < ρ)
    (hnear : infDist x0 Γ ≤ 2 * ρ) :
    doublingAt (volume : Measure LatticeSpace) (circleWeight Γ α)
      (ENNReal.ofReal ((256 : ℝ) ^ (α / 2) * (4 * 2) ^ 3)) x0 ρ := by
  obtain ⟨x1, hx1, hh, -⟩ := circle_shift_point x0 c hρ
  have hβ : 0 ≤ α / 2 := by positivity
  have hup : ∀ z ∈ ball x0 (2 * ρ), circleWeight Γ α z ≤ (1 + (4 * ρ) ^ 2) ^ (α / 2) := by
    intro z hz
    rw [mem_ball] at hz
    have h1 : infDist z Γ ≤ infDist x0 Γ + dist z x0 := infDist_le_infDist_add_dist
    have h2 := pow_le_pow_left₀ (infDist_nonneg (x := z) (s := Γ))
      (by linarith : infDist z Γ ≤ 4 * ρ) 2
    unfold circleWeight
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ
  have hlow : ∀ y ∈ ball x1 (ρ / 4), (1 + (ρ / 4) ^ 2) ^ (α / 2) ≤ circleWeight Γ α y := by
    intro y hy
    rw [mem_ball] at hy
    have h1 := circleLike_height_le_infDist h y
    have h2 := lattice_cell_coord_le_dist x1 y 2
    have h3 := abs_sub_le (x1 2) (y 2) (c 2)
    rw [dist_comm x1 y] at h2
    have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ρ / 4)
      (by linarith : ρ / 4 ≤ infDist y Γ) 2
    unfold circleWeight
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ
  have hMm : (1 + (4 * ρ) ^ 2) ^ (α / 2) ≤ (256 : ℝ) ^ (α / 2) * (1 + (ρ / 4) ^ 2) ^ (α / 2) :=
    circle_rpow_le_of_base_le (by norm_num) hβ (by nlinarith [sq_nonneg ρ])
  have hB1 : ball x1 (ρ / 4) ⊆ ball x0 ρ := ball_subset_ball' (by rw [hx1]; linarith)
  exact circle_mass_le_of_bounds (by norm_num) (by positivity) hB1 hup hlow hMm

/-- `CircleNearPremise alpha` follows, for `alpha >= 0`, from its Poincare
half alone. -/
theorem circleNearPremise_of_poincare {alpha : ℝ} (halpha : 0 ≤ alpha)
    (h : ∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
          rho ≤ R * Real.sin theta / 6 →
          Metric.infDist x0 (latitudeCircle R theta) ≤ 2 * rho →
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) P 1 x0 rho) :
    CircleNearPremise alpha := by
  obtain ⟨P, hP, hp⟩ := h
  exact ⟨ENNReal.ofReal ((256 : ℝ) ^ (alpha / 2) * (4 * 2) ^ 3), P, ENNReal.ofReal_ne_top, hP,
    fun R theta hR hθ hθ' x0 rho hρ0 hρ hn =>
      ⟨circle_near_doubling (latitudeCircle_circleLike hR hθ hθ') halpha hρ0 hn,
        hp R theta hR hθ hθ' x0 rho hρ0 hρ hn⟩⟩

end BrownRadial
