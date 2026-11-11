import CircleLocal
import CubeGrid

/-!
`lem:circle` of the paper, second part and assembly: the weight
`(1 + dist(x, C)^2)^(alpha/2)` of a horizontal circle `C` is doubling and
satisfies the Poincare inequality on all balls, with constants that do not
depend on the circle, modulo named premises.

Notation as in `CircleLocal`: `C = latitudeCircle R theta`, Euclidean radius
`a = R sin theta`, centre `c = latitudeCenter R theta`.

* Scales `rho >= a / 6` (`circle_large_ball_weak_poincare`): `lem:glue` in
  the paper's form (`gluing_lemma_of_local_doubling`), with
  `nu` the radial weight about `c` and the grid of side `h = a / 16` of
  `CubeGrid`. (G1) is the mass comparison for cubes of `CircleLocal`; (G2) is
  `circle_small_ball`, because the balls `B_j` have radius
  `0.163 a < a / 6`; the Poincare inequality of `nu` at `2B` is
  `RadialWeightPremise`. The result is the weak inequality, energy over `4B`.
  Nothing in this step uses `a > 16`.
* All balls, uniformly in the circle: doubling (`circle_doubling_all`) and
  the weak inequality (`circle_weak_poincare_all`), from `RadialWeightPremise`
  and `CircleNearPremise`.
* The strong inequality at all balls needs the self-improvement of Hajlasz
  and Koskela. **The premise `SelfImprovementPremise` of `DoublingPoincare`
  is per weight**: it gives, for each weight separately, some finite
  constant, and says nothing on what that constant depends on. Applied one
  circle at a time it yields `circle_lemma_each_circle`, where the Poincare
  constant may depend on the circle. `CircleLemmaPremise` asks for one
  constant for all circles of the lattice. This file therefore states the
  quantitative form `SelfImprovementUniformPremise` (the constant of the
  strong inequality depends only on the doubling constant and on the constant
  of the weak inequality), which implies `SelfImprovementPremise`
  (`selfImprovementPremise_of_uniform`), and proves `CircleLemmaPremise` from
  it (`circleLemmaPremise_of_premises`).
* The end results of `thm:B` are restated with `RadialWeightPremise`,
  `CircleNearPremise` and `SelfImprovementUniformPremise` in place of
  `CircleLemmaPremise` and `SelfImprovementPremise`. **In every theorem of
  this file whose name ends in `of_premises` or contains
  `modulo_radial_near`, the hypothesis `hself` is the quantitative
  `SelfImprovementUniformPremise`, not `SelfImprovementPremise`.**
* `circleLemmaPremise_of_poincare_premises`: the same from the Poincare
  halves of the two new premises, their doubling halves being proved in
  `CircleLocal`.
* `CircleLemmaPremise 0` holds outright.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### Scales `rho >= a / 6`: gluing -/

/-- **Scales `rho >= a / 6`, weak Poincare** (paper, second part of the proof
of `lem:circle`). The circle weight satisfies the Poincare inequality with
energy over the 4-fold ball at every ball of radius at least `a / 6`,
`a = R sin theta`, with one constant for all circles and all such balls. No
lower bound on `a` is used. -/
theorem circle_large_ball_weak_poincare {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (x0 : LatticeSpace) (rho : ℝ), R * Real.sin theta / 6 ≤ rho →
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) K 4 x0 rho := by
  obtain ⟨Ds, Ps, hDs, hPs, hsmall⟩ := circle_small_ball halpha hnear
  obtain ⟨Dr, Pr, -, hPr, hrad⟩ := hradial
  obtain ⟨K, hK, hglue⟩ := gluing_lemma_of_local_doubling.{0} 3 (κ := 101 / 100) (by norm_num)
    8 216 1 (326 / 125) (G := ENNReal.ofReal (circleMassConst 2 32 alpha)) (P := Ps) (D := Ds)
    (Pν := Pr) ENNReal.ofReal_ne_top hPs hDs hPr
  refine ⟨K, hK, fun R theta hR hθ hθ' x0 rho hρ => ?_⟩
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  obtain ⟨h, hha⟩ : ∃ h : ℝ, R * Real.sin theta = 16 * h := ⟨R * Real.sin theta / 16, by ring⟩
  have hh : 0 < h := by linarith
  obtain ⟨hfin, hcov, hN0, hdiam, hΛ, hball, hRs, hin, hNb⟩ :=
    grid_gluing_hypotheses hh x0 (ρ := rho) (by linarith)
  haveI : Fintype (gridIndex h x0 rho) := hfin.fintype
  have hv : Continuous fun x : LatticeSpace =>
      (1 + ‖x - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2) := by
    rw [← circleWeight_singleton]
    exact circleWeight_continuous _ _
  refine hglue (gridIndex h x0 rho) (fun z => gridCenter h z) (fun _ => h)
    (fun z => gridCenter h z) (fun _ => 163 / 1000 * (16 * h))
    (circleWeight (latitudeCircle R theta) alpha)
    (fun x => (1 + ‖x - latitudeCenter R theta‖ ^ 2) ^ (alpha / 2)) x0 rho
    (circleWeight_continuous _ _) (fun x => (circleWeight_pos _ _ x).le) hv (fun _ => hh)
    hcov hN0 hdiam hΛ hball hRs hin hNb
    (fun z => (circle_mass_cube_comparable hR hθ hθ' halpha (gridCenter h z) (h := h)
      (by linarith)).1)
    (fun z => (circle_mass_cube_comparable hR hθ hθ' halpha (gridCenter h z) (h := h)
      (by linarith)).2)
    (fun z => (hsmall R theta hR hθ hθ' (gridCenter h z) (163 / 1000 * (16 * h))
      (by positivity) (by linarith)).2)
    (fun z a _ r hr0 hr => (hsmall R theta hR hθ hθ' a r hr0 (by linarith)).1)
    ((hrad (latitudeCenter R theta)).2 x0 (2 * rho) (by linarith))

/-! ### All balls, uniformly in the circle -/

/-- **Doubling at all balls**, one constant for all horizontal circles:
`rho <= a / 6` by `circle_small_ball`, `rho >= a / 6` by the mass comparison
and doubling of the radial weight (the paper's route). -/
theorem circle_doubling_all {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        doublingAll (volume : Measure LatticeSpace)
          (circleWeight (latitudeCircle R theta) alpha) D := by
  obtain ⟨Ds, Ps, hDs, -, hsmall⟩ := circle_small_ball halpha hnear
  obtain ⟨Dl, hDl, hlarge⟩ := circle_large_ball_doubling halpha hradial
  refine ⟨max Ds Dl, (max_lt hDs.lt_top hDl.lt_top).ne, fun R theta hR hθ hθ' a r hr => ?_⟩
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  rcases le_total r (R * Real.sin theta / 6) with h | h
  · exact doublingAt_mono (le_max_left _ _) (hsmall R theta hR hθ hθ' a r hr h).1
  · exact doublingAt_mono (le_max_right _ _) (hlarge R theta hR hθ hθ' a r (by linarith))

/-- Doubling at all balls from `CircleNearPremise` alone: above the scale
`a / 6` the direct mass bound replaces doubling of the radial weight. Not the
paper's route. -/
theorem circle_doubling_all_of_near {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hnear : CircleNearPremise alpha) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        doublingAll (volume : Measure LatticeSpace)
          (circleWeight (latitudeCircle R theta) alpha) D := by
  obtain ⟨Ds, Ps, hDs, -, hsmall⟩ := circle_small_ball halpha hnear
  refine ⟨max Ds (ENNReal.ofReal (circleMassConst 2 16 alpha)),
    (max_lt hDs.lt_top ENNReal.ofReal_lt_top).ne, fun R theta hR hθ hθ' a r hr => ?_⟩
  have ha0 : 0 < R * Real.sin theta := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ hθ')
  rcases le_total r (R * Real.sin theta / 6) with h | h
  · exact doublingAt_mono (le_max_left _ _) (hsmall R theta hR hθ hθ' a r hr h).1
  · exact doublingAt_mono (le_max_right _ _)
      (circle_large_ball_doubling_direct hR hθ hθ' halpha a (by linarith))

/-- **Weak Poincare at all balls**, energy over the 4-fold ball, one constant
for all horizontal circles: `rho <= a / 6` by the strong inequality of
`circle_small_ball`, `rho >= a / 6` by gluing. The two ranges meet at
`rho = a / 6`; there is no gap. -/
theorem circle_weak_poincare_all {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha) :
    ∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) P 4 a r := by
  obtain ⟨Ds, Ps, -, hPs, hsmall⟩ := circle_small_ball halpha hnear
  obtain ⟨K, hK, hlarge⟩ := circle_large_ball_weak_poincare halpha hradial hnear
  refine ⟨max Ps K, (max_lt hPs.lt_top hK.lt_top).ne, fun R theta hR hθ hθ' a r hr => ?_⟩
  rcases le_total r (R * Real.sin theta / 6) with h | h
  · exact poincareAt_mono (le_max_left _ _)
      (poincareAt_weak_of_strong (by norm_num) (hsmall R theta hR hθ hθ' a r hr h).2)
  · exact poincareAt_mono (le_max_right _ _) (hlarge R theta hR hθ hθ' a r h)

/-! ### Self-improvement -/

/-- With `SelfImprovementPremise` as stated in `DoublingPoincare`: for every
horizontal circle the weight is doubling on all balls, with one constant for
all circles, and satisfies the strong Poincare inequality on all balls with a
constant that **may depend on the circle**. That premise says nothing on how
the constant of the strong inequality depends on the weight, so this is what
the argument gives from it; it is short of `CircleLemmaPremise`. -/
theorem circle_lemma_each_circle {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha)
    (hself : SelfImprovementPremise) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        doublingAll (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D ∧
          ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
            poincareAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) P 1 a r := by
  obtain ⟨D, hD, hd⟩ := circle_doubling_all halpha hradial hnear
  obtain ⟨K, hK, hk⟩ := circle_weak_poincare_all halpha hradial hnear
  exact ⟨D, hD, fun R theta hR hθ hθ' => ⟨hd R theta hR hθ hθ',
    hself _ (circleWeight_continuous _ _) (circleWeight_pos _ _) ⟨D, hD, hd R theta hR hθ hθ'⟩
      ⟨K, hK, hk R theta hR hθ hθ'⟩⟩⟩

/-- Self-improvement, quantitative form (Hajlasz and Koskela, Thms 5.1 and
9.7, read with the dependence of the constants): for continuous positive
weights on three-space, the constant of the strong Poincare inequality is
bounded in terms of the doubling constant and of the constant of the weak
inequality (energy over the 4-fold ball) alone. A statement only. It differs
from `SelfImprovementPremise` in the order of the quantifiers and implies it
(`selfImprovementPremise_of_uniform`). -/
def SelfImprovementUniformPremise : Prop :=
  ∀ D K : ℝ≥0∞, D ≠ ⊤ → K ≠ ⊤ → ∃ P : ℝ≥0∞, P ≠ ⊤ ∧
    ∀ w : LatticeSpace → ℝ, Continuous w → (∀ x, 0 < w x) →
      doublingAll (volume : Measure LatticeSpace) w D →
      (∀ (a : LatticeSpace) (r : ℝ), 0 < r →
        poincareAt (volume : Measure LatticeSpace) w K 4 a r) →
      ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
        poincareAt (volume : Measure LatticeSpace) w P 1 a r

/-- The quantitative form implies the form of `DoublingPoincare`. -/
theorem selfImprovementPremise_of_uniform (h : SelfImprovementUniformPremise) :
    SelfImprovementPremise := by
  rintro w hw hpos ⟨D, hD, hd⟩ ⟨K, hK, hk⟩
  obtain ⟨P, hP, hp⟩ := h D K hD hK
  exact ⟨P, hP, hp w hw hpos hd hk⟩

/-- **`lem:circle`, modulo the three premises.** For `alpha >= 0` and every
horizontal circle `C` in three-space, of any radius `a > 0`: the weight
`(1 + dist(x, C)^2)^(alpha/2)` is doubling on all balls and satisfies the
strong Poincare inequality on all balls, with constants that do not depend on
the circle. As in the paper, circles with `a <= 16` are handled by comparison
with the radial weight and circles with `a > 16` by gluing and
self-improvement; the second argument does not use `a > 16`. -/
theorem circle_lemma_of_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha)
    (hself : SelfImprovementUniformPremise) :
    ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        doublingAll (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D ∧
          ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
            poincareAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) P 1 a r := by
  obtain ⟨D, hD, hd⟩ := circle_doubling_all halpha hradial hnear
  obtain ⟨K, hK, hk⟩ := circle_weak_poincare_all halpha hradial hnear
  obtain ⟨P, hP, hp⟩ := hself D K hD hK
  obtain ⟨Ds, Ps, hDs, hPs, hs⟩ := circle_small_radius_all_balls halpha hradial
  refine ⟨max Ds D, max Ps P, (max_lt hDs.lt_top hD.lt_top).ne,
    (max_lt hPs.lt_top hP.lt_top).ne, fun R theta hR hθ hθ' => ?_⟩
  rcases le_or_gt (R * Real.sin theta) 16 with ha | _
  · obtain ⟨h1, h2⟩ := hs R theta hR hθ hθ' ha
    exact ⟨doublingAll_mono (le_max_left _ _) h1,
      fun a r hr => poincareAt_mono (le_max_left _ _) (h2 a r hr)⟩
  · exact ⟨doublingAll_mono (le_max_right _ _) (hd R theta hR hθ hθ'),
      fun a r hr => poincareAt_mono (le_max_right _ _)
        (hp _ (circleWeight_continuous _ _) (circleWeight_pos _ _) (hd R theta hR hθ hθ')
          (hk R theta hR hθ hθ') a r hr)⟩

/-- **`CircleLemmaPremise` from the three premises**, for `alpha >= 0`: the
radial weight (Bjorn), the near-circle step of the paper, and the
self-improvement in its quantitative form. -/
theorem circleLemmaPremise_of_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialWeightPremise alpha) (hnear : CircleNearPremise alpha)
    (hself : SelfImprovementUniformPremise) : CircleLemmaPremise alpha := by
  obtain ⟨D, P, hD, hP, h⟩ :=
    circle_lemma_of_premises halpha hradial hnear hself
  refine ⟨D, P, hD, hP, fun k _ i j => ?_⟩
  obtain ⟨R, θ, hR, hθ, hθ', he⟩ := indexedLatticeCircle_eq_latitudeCircle k i j
  rw [he]
  exact h R θ hR hθ hθ'

/-- `CircleLemmaPremise` from the Poincare halves of `RadialWeightPremise`
and `CircleNearPremise` and the quantitative self-improvement: the doubling
halves of the two premises are theorems for `alpha >= 0`. -/
theorem circleLemmaPremise_of_poincare_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (c a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace)
        (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2)) P 1 a r)
    (hnear : ∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
          rho ≤ R * Real.sin theta / 6 →
          Metric.infDist x0 (latitudeCircle R theta) ≤ 2 * rho →
          poincareAt (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) P 1 x0 rho)
    (hself : SelfImprovementUniformPremise) : CircleLemmaPremise alpha :=
  circleLemmaPremise_of_premises halpha (radialWeightPremise_of_poincare halpha hradial)
    (circleNearPremise_of_poincare halpha hnear) hself

/-! ### `thm:B` without `CircleLemmaPremise` -/

/-- **`thm:B`(a)**: for every `alpha >= 0` the lattice weight is doubling on
all balls and satisfies the strong Poincare inequality on all balls, modulo
the radial weight, the near-circle step and the self-improvement in its
quantitative form. -/
theorem theorem_B_a_modulo_radial_near_and_self_improvement {alpha : ℝ}
    (halpha : 0 ≤ alpha) (hradial : RadialWeightPremise alpha)
    (hnear : CircleNearPremise alpha) (hself : SelfImprovementUniformPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 a r) :=
  theorem_B_a_modulo_circle_and_self_improvement halpha
    (circleLemmaPremise_of_premises halpha hradial hnear hself)
    (selfImprovementPremise_of_uniform hself)

/-- `thm:B`(a) with the Poincare inequality in the form `ballPoincare`. -/
theorem theorem_B_a_ball_poincare_modulo_radial_near_and_self_improvement {alpha : ℝ}
    (halpha : 0 ≤ alpha) (hradial : RadialWeightPremise alpha)
    (hnear : CircleNearPremise alpha) (hself : SelfImprovementUniformPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ballPoincare (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) P) :=
  theorem_B_a_ball_poincare_modulo_circle_and_self_improvement halpha
    (circleLemmaPremise_of_premises halpha hradial hnear hself)
    (selfImprovementPremise_of_uniform hself)

/-- **`thm:B`, conclusion**, for `alpha >= 4`: the lattice weight and its
Gaussian marginal are not parabolic, modulo the radial weight, the
near-circle step, the self-improvement in its quantitative form and the
volume criterion. -/
theorem theorem_B_modulo_radial_near_self_improvement_and_volume {alpha : ℝ≥0}
    (halpha : 4 ≤ (alpha : ℝ)) (hradial : RadialWeightPremise alpha)
    (hnear : CircleNearPremise alpha) (hself : SelfImprovementUniformPremise)
    (hvol : VolumeCriterionPremise) :
    ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
    ¬ parabolic (volume : Measure LatticeSpace)
      (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha)) :=
  theorem_B_modulo_circle_self_improvement_and_volume halpha
    (circleLemmaPremise_of_premises (by linarith) hradial hnear hself)
    (selfImprovementPremise_of_uniform hself) hvol

/-- **`thm:B`, all parts**, for `alpha >= 4`, modulo the same four premises. -/
theorem theorem_B_statement_modulo_radial_near_self_improvement_and_volume
    {alpha : ℝ≥0} (halpha : 4 ≤ (alpha : ℝ)) (hradial : RadialWeightPremise alpha)
    (hnear : CircleNearPremise alpha) (hself : SelfImprovementUniformPremise)
    (hvol : VolumeCriterionPremise) :
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
  theorem_B_statement_modulo_circle_self_improvement_and_volume halpha
    (circleLemmaPremise_of_premises (by linarith) hradial hnear hself)
    (selfImprovementPremise_of_uniform hself) hvol

/-! ### Exponent zero -/

theorem circleWeight_zero (C : Set LatticeSpace) : circleWeight C 0 = fun _ => 1 := by
  funext x
  simp [circleWeight]

/-- `CircleLemmaPremise 0` holds outright: the weight is identically one, so
the constants are those of Lebesgue measure, `8` and `32`. In particular the
premise is not contradictory. -/
theorem circleLemmaPremise_zero : CircleLemmaPremise 0 := by
  refine ⟨8, 32, by norm_num, by norm_num, fun k _ i j => ?_⟩
  rw [circleWeight_zero]
  exact ⟨lebesgue_doublingAll_three, fun a r _ => lebesgue_poincareAt_three a r⟩

end BrownRadial
