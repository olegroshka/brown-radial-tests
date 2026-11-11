import CircleLemma

/-!
Closing statements for `thm:B` of the paper, and the constant of the cell-mass
paragraph.

1. `RadialPoincarePremise alpha` and `CircleNearPoincarePremise alpha`: the
   Poincare halves of `RadialWeightPremise` and `CircleNearPremise`, named.
   For `alpha >= 0` each is equivalent to the full premise, because the
   doubling halves are theorems (`radial_weight_doublingAll`,
   `circle_near_doubling`).
2. The end results with the weakest hypotheses available: `lem:circle` for all
   horizontal circles, `thm:B`(a) in both forms, the conclusion of `thm:B` and
   the statement with all parts. **Three premises remain for part (a), four
   for the conclusion. They are hypotheses of the theorems below; none of them
   is proved in this project.**
   * `SelfImprovementUniformPremise`: Hajlasz and Koskela, Sobolev met
     Poincare, Cor. 9.8 (Thm 9.7 with Cor. 9.5), with the statements on the
     constants on pp. 23 and 44. Sturm, part III, Thm 2.4, states the same
     uniform dependence for a weak inequality with energy over `2B`; the
     premise assumes less (energy over `4B`), so Cor. 9.8 is the matching
     source. Read, not formalized.
   * `RadialPoincarePremise alpha`: Bjorn 2001, Prop. 6 with `k = n = 3`,
     followed by the self-improvement; or directly Grigor'yan and
     Saloff-Coste 2005, Prop. 4.9 with Thm 2.7. Read, not formalized.
   * `CircleNearPoincarePremise alpha`: the near-circle step of the paper's
     own proof of `lem:circle` (paper, lines 807--821). **This is not a
     published theorem.** It was audited by hand and is not formalized.
   * `VolumeCriterionPremise` (conclusion only): Sturm, part III, Cor. 4.11
     and Cor. 4.12 (p. 294, with Example 5 B), stated with the Green function
     and with "recurrent". The passage to zero capacity of the unit ball is
     Fukushima, Oshima and Takeda, Dirichlet forms and symmetric Markov
     processes (2nd ed.), Lemma 1.5.3 (p. 39), or Thm 1.6.3 (p. 58), with
     written steps for a continuous positive weight
     (`notes/lean_sessions/reports/U2_sources.md`, section 1.3). Read, not
     formalized.
3. Cell mass (paper, lines 900--914, and the draft replacement of that
   paragraph): for a centre in shell `k >= 4`, `s_k = sqrt (2^k)`,
   * a ball `B` of radius in `[s_k / 64, s_k]`:
     `(1/24) 65537^(-alpha/2) |B| <= mu(B) <= |B|`;
   * a closed cube `Q` of side in `[s_k / 32, s_k]`:
     `(1/48) 65537^(-alpha/2) |Q| <= mu(Q) <= |Q|`;
   and the doubling bound of line 931 with the constants
   `192 * 65537^(alpha/2)` and (weaker, the draft's) `384 * 65537^(alpha/2)`.
   The route is the draft's: `lattice_mass_good_volume` with `r = s_k / 64`,
   `lattice_cell_weight_lower` with `eps = 1 / 128`, `lattice_cell_norm_le`.
4. Two hand counterexamples of the first pass, as theorems:
   `poincareAt_transfer_local` fails for the dilation `lam = 0`
   (`poincareAt_transfer_local_fails_lam_zero`), and a partition of unity
   that sums to one on the union of the enlarged intervals cannot have a
   derivative bounded by a constant over the side there
   (`partition_gradient_unbounded_on_enlarged`).
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownRadial

/-! ### The two Poincare-only premises -/

/-- Poincare half of `RadialWeightPremise`: for every centre `c` the weight
`(1 + |x - c|^2)^(alpha/2)` on three-space satisfies the strong Poincare
inequality on all balls, with a constant that does not depend on `c`.
Published: Bjorn 2001, Prop. 6 with `k = n = 3`, then Hajlasz and Koskela,
Cor. 9.8; directly, Grigor'yan and Saloff-Coste 2005, Prop. 4.9 with Thm 2.7.
A statement only; this is the hypothesis `hradial` of
`circleLemmaPremise_of_poincare_premises`. -/
def RadialPoincarePremise (alpha : ℝ) : Prop :=
  ∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (c a : LatticeSpace) (r : ℝ), 0 < r →
    poincareAt (volume : Measure LatticeSpace)
      (fun x => (1 + ‖x - c‖ ^ 2) ^ (alpha / 2)) P 1 a r

/-- Poincare half of `CircleNearPremise`: for every horizontal circle of
Euclidean radius `a = R sin theta` and every ball `B(x_0, rho)` with
`rho <= a / 6` and `dist(x_0, C) <= 2 rho`, the circle weight satisfies the
strong Poincare inequality at that ball, with a constant that depends on
neither the circle nor the ball. This is the near-circle step of the paper's
own proof of `lem:circle` (lines 807--821: Fermi coordinates, cylinder
weight, John domain). **Not a published theorem and not formalized**; audited
by hand. A statement only; this is the hypothesis `hnear` of
`circleLemmaPremise_of_poincare_premises`. -/
def CircleNearPoincarePremise (alpha : ℝ) : Prop :=
  ∃ P : ℝ≥0∞, P ≠ ⊤ ∧
    ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
      ∀ (x0 : LatticeSpace) (rho : ℝ), 0 < rho →
        rho ≤ R * Real.sin theta / 6 →
        Metric.infDist x0 (latitudeCircle R theta) ≤ 2 * rho →
        poincareAt (volume : Measure LatticeSpace)
          (circleWeight (latitudeCircle R theta) alpha) P 1 x0 rho

/-- For `alpha >= 0`, `RadialWeightPremise alpha` is equivalent to its
Poincare half. The direction from left to right needs no condition on
`alpha`. -/
theorem radialWeightPremise_iff_poincare {alpha : ℝ} (halpha : 0 ≤ alpha) :
    RadialWeightPremise alpha ↔ RadialPoincarePremise alpha := by
  constructor
  · rintro ⟨D, P, -, hP, h⟩
    exact ⟨P, hP, fun c a r hr => (h c).2 a r hr⟩
  · exact fun h => radialWeightPremise_of_poincare halpha h

/-- For `alpha >= 0`, `CircleNearPremise alpha` is equivalent to its Poincare
half. The direction from left to right needs no condition on `alpha`. -/
theorem circleNearPremise_iff_poincare {alpha : ℝ} (halpha : 0 ≤ alpha) :
    CircleNearPremise alpha ↔ CircleNearPoincarePremise alpha := by
  constructor
  · rintro ⟨D, P, -, hP, h⟩
    exact ⟨P, hP, fun R theta hR hθ hθ' x0 rho hρ0 hρ hn =>
      (h R theta hR hθ hθ' x0 rho hρ0 hρ hn).2⟩
  · exact fun h => circleNearPremise_of_poincare halpha h

/-- `CircleLemmaPremise` from the two named Poincare premises and the
self-improvement with uniform constants. The two definitions above are,
word for word, the hypotheses of `circleLemmaPremise_of_poincare_premises`,
which is applied here unchanged. The three hypotheses are premises, not
proved here. -/
theorem circleLemmaPremise_of_named_poincare_premises {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) : CircleLemmaPremise alpha :=
  circleLemmaPremise_of_poincare_premises halpha hradial hnear hself

/-! ### The end results -/

/-- **`lem:circle`, final form.** For `alpha >= 0` and every horizontal circle
`C` in three-space, of any radius: the weight `(1 + dist(x, C)^2)^(alpha/2)`
is doubling on all balls and satisfies the strong Poincare inequality on all
balls, with constants that do not depend on the circle.

The three hypotheses are premises, not proved here:
* `hradial`: the radial weight (Bjorn 2001, Prop. 6 with `k = n = 3`, with
  the self-improvement; or Grigor'yan and Saloff-Coste 2005, Prop. 4.9 with
  Thm 2.7);
* `hnear`: the near-circle step of the paper's own proof (lines 807--821),
  audited by hand, not a published theorem, not formalized;
* `hself`: the self-improvement with uniform constants (Hajlasz and Koskela,
  Cor. 9.8, constants on pp. 23 and 44; compare Sturm, part III, Thm 2.4). -/
theorem circle_lemma_final {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) :
    ∃ D P : ℝ≥0∞, D ≠ ⊤ ∧ P ≠ ⊤ ∧
      ∀ (R theta : ℝ), 0 < R → 0 < theta → theta < Real.pi →
        doublingAll (volume : Measure LatticeSpace)
            (circleWeight (latitudeCircle R theta) alpha) D ∧
          ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
            poincareAt (volume : Measure LatticeSpace)
              (circleWeight (latitudeCircle R theta) alpha) P 1 a r :=
  circle_lemma_of_premises halpha ((radialWeightPremise_iff_poincare halpha).mpr hradial)
    ((circleNearPremise_iff_poincare halpha).mpr hnear) hself

/-- **`thm:B`(a), final form.** For every `alpha >= 0` the lattice weight is
doubling on all balls and satisfies the strong Poincare inequality
`(eq:poincare)` on all balls.

The three hypotheses are premises, not proved here:
* `hradial`: the radial weight (Bjorn 2001, Prop. 6 with `k = n = 3`, with
  the self-improvement; or Grigor'yan and Saloff-Coste 2005, Prop. 4.9 with
  Thm 2.7);
* `hnear`: the near-circle step of the paper's own proof of `lem:circle`
  (lines 807--821), audited by hand, not a published theorem, not formalized;
* `hself`: the self-improvement with uniform constants (Hajlasz and Koskela,
  Cor. 9.8, constants on pp. 23 and 44; compare Sturm, part III, Thm 2.4).
Everything else in the written proof of part (a) is proved: the local
comparison, the cell mass, the small balls, the covering, `lem:glue`, the
Poincare inequality of Lebesgue measure, and the reduction of `lem:circle` to
the first two premises. -/
theorem theorem_B_a_final {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧ ∀ (a : LatticeSpace) (r : ℝ), 0 < r →
      poincareAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha)
        P 1 a r) :=
  theorem_B_a_modulo_radial_near_and_self_improvement halpha
    ((radialWeightPremise_iff_poincare halpha).mpr hradial)
    ((circleNearPremise_iff_poincare halpha).mpr hnear) hself

/-- **`thm:B`(a), final form, with the Poincare inequality as `ballPoincare`**:
variance about the weighted mean, energy over the ball, tests C1 on the
closed ball. Same three premises as `theorem_B_a_final` (radial weight:
Bjorn, or Grigor'yan and Saloff-Coste; near-circle step: the paper's own
argument, not a published theorem; self-improvement: Hajlasz and Koskela,
Cor. 9.8); none is proved here. -/
theorem theorem_B_a_ball_poincare_final {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) :
    (∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      doublingAll (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) D) ∧
    (∃ P : ℝ≥0∞, P ≠ ⊤ ∧
      ballPoincare (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) P) :=
  theorem_B_a_ball_poincare_modulo_radial_near_and_self_improvement halpha
    ((radialWeightPremise_iff_poincare halpha).mpr hradial)
    ((circleNearPremise_iff_poincare halpha).mpr hnear) hself

/-- **`thm:B`, conclusion, final form**, for `alpha >= 4`: the lattice weight
and its Gaussian marginal are not parabolic.

The four hypotheses are premises, not proved here: the three of
`theorem_B_a_final` (radial weight: Bjorn 2001, Prop. 6 with `k = n = 3`, or
Grigor'yan and Saloff-Coste 2005, Prop. 4.9 with Thm 2.7; near-circle step:
the paper's lines 807--821, hand-audited, not a published theorem;
self-improvement: Hajlasz and Koskela, Cor. 9.8, pp. 23 and 44) and
* `hvol`: the cited direction of the volume criterion `thm:volume` for
  continuous positive weights (Sturm, part III, Cor. 4.11 and Cor. 4.12 with
  Example 5 B; the passage from the Green function, or from "recurrent", to
  zero capacity is Fukushima, Oshima and Takeda, Lemma 1.5.3 or Thm 1.6.3,
  with written steps; read, not formalized). -/
theorem theorem_B_final {alpha : ℝ≥0} (halpha : 4 ≤ (alpha : ℝ))
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) (hvol : VolumeCriterionPremise) :
    ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys alpha) ∧
    ¬ parabolic (volume : Measure LatticeSpace)
      (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys alpha)) :=
  theorem_B_modulo_radial_near_self_improvement_and_volume halpha
    ((radialWeightPremise_iff_poincare (by linarith)).mpr hradial)
    ((circleNearPremise_iff_poincare (by linarith)).mpr hnear) hself hvol

/-- **`thm:B`, all parts, final form**, for `alpha >= 4`: (a) doubling and
Poincare on all balls; (b) the sphere test, the ray test and the volume test
are silent; (c) the volume of balls grows like `r^3`; and the weight and its
Gaussian marginal are not parabolic. Parts (b) and (c) use no premise. Part
(a) uses `hradial`, `hnear`, `hself`; the last part uses `hvol` as well. The
four are premises, not proved here; sources as in `theorem_B_final`. -/
theorem theorem_B_statement_final {alpha : ℝ≥0} (halpha : 4 ≤ (alpha : ℝ))
    (hradial : RadialPoincarePremise alpha) (hnear : CircleNearPoincarePremise alpha)
    (hself : SelfImprovementUniformPremise) (hvol : VolumeCriterionPremise) :
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
  theorem_B_statement_modulo_radial_near_self_improvement_and_volume halpha
    ((radialWeightPremise_iff_poincare (by linarith)).mpr hradial)
    ((circleNearPremise_iff_poincare (by linarith)).mpr hnear) hself hvol

/-! ### Cell mass in shell `k`, with the constant `65537^(-alpha/2)` -/

/-- `(1 / 65537)^b = 65537^(-b)`. -/
theorem lattice_shell_const_rpow (b : ℝ) : (1 / 65537 : ℝ) ^ b = (65537 : ℝ) ^ (-b) := by
  rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]

/-- The cell radius `r = s_k / 64` is admissible for the three-point lemma
`lattice_cell_far_point` at every point within `s_k` of a centre in shell
`k >= 4`: `64 r^2 <= 1 + |y|`. -/
theorem lattice_shell_three_point_scale {k : ℕ} (hk : 4 ≤ k) {x0 y : LatticeSpace}
    (h1 : (2:ℝ)^k ≤ ‖x0‖) (hy : dist y x0 ≤ Real.sqrt ((2:ℝ)^k)) :
    64 * (Real.sqrt ((2:ℝ)^k) / 64)^2 ≤ 1 + ‖y‖ := by
  have hS := lattice_local_scale_ge hk
  have hsq : Real.sqrt ((2:ℝ)^k) ^ 2 = (2:ℝ)^k := Real.sq_sqrt (by positivity)
  have hn := (lattice_local_norm_dist y x0).2
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt ((2:ℝ)^k))
    (by linarith : (0:ℝ) ≤ Real.sqrt ((2:ℝ)^k) - 4)]

/-- Where `d >= s_k / 128`, within `s_k` of a centre in shell `k >= 4`, the
weight is at least `65537^(-alpha/2)`: the paper's bound
`(eps^2 / (4 + eps^2))^(alpha/2)` at `eps = 1 / 128`. -/
theorem lattice_shell_weight_lower {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {x0 x : LatticeSpace} (h2 : ‖x0‖ < (2:ℝ)^(k+1))
    (hx : dist x x0 ≤ Real.sqrt ((2:ℝ)^k))
    (hd : Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys) :
    (65537:ℝ)^(-(α/2)) ≤ latticeWeight latticeValleys α x := by
  have h := lattice_cell_weight_lower hα (k := k) (x := x) (ε := 1/128) (by norm_num)
    (by linarith) (lattice_cell_norm_le hk h2 hx)
  have e : (1/128 : ℝ)^2 / (4 + (1/128 : ℝ)^2) = 1 / 65537 := by norm_num
  rwa [e, lattice_shell_const_rpow] at h

/-- **Cell mass, balls, lower bound.** Centre in shell `k >= 4`, radius in
`[s_k / 64, s_k]`: `(1/24) 65537^(-alpha/2) |B| <= mu(B)`. Three translates
of the set `{d >= s_k / 128}` cover the ball of half the radius. -/
theorem lattice_shell_ball_mass_lower {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {x0 : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖x0‖) (h2 : ‖x0‖ < (2:ℝ)^(k+1)) {ρ : ℝ}
    (hlo : Real.sqrt ((2:ℝ)^k) / 64 ≤ ρ) (hhi : ρ ≤ Real.sqrt ((2:ℝ)^k)) :
    ENNReal.ofReal ((1/24) * (65537:ℝ)^(-(α/2))) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) := by
  have hS := lattice_local_scale_ge hk
  have hr : 0 < Real.sqrt ((2:ℝ)^k) / 64 := by linarith
  have hGmeas : MeasurableSet
      ({x : LatticeSpace | Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys} ∩
        ball x0 ρ) :=
    (isClosed_le continuous_const (continuous_infDist_pt _)).measurableSet.inter
      measurableSet_ball
  have hgood : volume (ball x0 (ρ - Real.sqrt ((2:ℝ)^k) / 64 / 2)) ≤
      3 * volume ({x : LatticeSpace |
        Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) := by
    apply lattice_mass_good_volume hr
    intro y hy
    rw [mem_ball] at hy
    exact lattice_shell_three_point_scale hk h1 (by linarith)
  have hhalf : volume (ball x0 ρ) ≤
      8 * volume (ball x0 (ρ - Real.sqrt ((2:ℝ)^k) / 64 / 2)) := by
    have h := lattice_mass_ball_scale x0 x0 (by norm_num : (0:ℝ) ≤ 2) (ρ/2)
    rw [show 2 * (ρ/2) = ρ by ring, show ENNReal.ofReal ((2:ℝ)^3) = 8 by norm_num] at h
    rw [h]
    gcongr
    linarith
  have hw : ∀ x ∈ {x : LatticeSpace |
        Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys} ∩ ball x0 ρ,
      (65537:ℝ)^(-(α/2)) ≤ latticeWeight latticeValleys α x := by
    intro x hx
    have hxb := hx.2
    rw [mem_ball] at hxb
    exact lattice_shell_weight_lower hα hk h2 (by linarith) hx.1
  have hmass := lattice_mass_ge_of_weight_ge hGmeas hw
  calc ENNReal.ofReal ((1/24) * (65537:ℝ)^(-(α/2))) * volume (ball x0 ρ)
      ≤ ENNReal.ofReal ((1/24) * (65537:ℝ)^(-(α/2))) * (8 * (3 *
          volume ({x : LatticeSpace |
            Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys} ∩ ball x0 ρ))) := by
        gcongr
        exact hhalf.trans (by gcongr)
    _ = ENNReal.ofReal ((65537:ℝ)^(-(α/2))) *
          volume ({x : LatticeSpace |
            Real.sqrt ((2:ℝ)^k) / 64 / 2 ≤ infDist x latticeValleys} ∩ ball x0 ρ) := by
        rw [← mul_assoc, ← mul_assoc, mul_assoc (ENNReal.ofReal _),
          show (8:ℝ≥0∞) * 3 = ENNReal.ofReal 24 by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ _ := hmass.trans (measure_mono inter_subset_right)

/-- **Cell mass, balls** (`(eq:cellmass)` for balls, with its constant).
Centre in shell `k >= 4`, radius `rho` in `[s_k / 64, s_k]`:
`(1/24) 65537^(-alpha/2) |B| <= mu(B) <= |B|`. The range contains the range
`[s_k / 32, s_k]` of the paper. -/
theorem lattice_shell_ball_mass {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {x0 : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖x0‖) (h2 : ‖x0‖ < (2:ℝ)^(k+1)) {ρ : ℝ}
    (hlo : Real.sqrt ((2:ℝ)^k) / 64 ≤ ρ) (hhi : ρ ≤ Real.sqrt ((2:ℝ)^k)) :
    ENNReal.ofReal ((1/24) * (65537:ℝ)^(-(α/2))) * volume (ball x0 ρ) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 ρ) ≤ volume (ball x0 ρ) :=
  ⟨lattice_shell_ball_mass_lower hα hk h1 h2 hlo hhi, lattice_mass_le_volume hα _⟩

/-- A closed cube of side `l` in three-space has at most twice the volume of
the inscribed ball: `l^3 <= 2 (4 pi / 3) (l / 2)^3`, because `pi >= 3`. -/
theorem lattice_shell_cube_volume_le (y : LatticeSpace) {l : ℝ} (hl : 0 ≤ l) :
    volume (cube y l) ≤ 2 * volume (ball y (l / 2)) := by
  rw [cube_volume y hl, EuclideanSpace.volume_ball_fin_three,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hpi := Real.pi_gt_three
  have h3 : 0 ≤ l ^ 3 := by positivity
  nlinarith [mul_nonneg h3 (by linarith : (0:ℝ) ≤ Real.pi - 3)]

/-- **Cell mass, closed cubes** (`(eq:cellmass)` for cubes, with its
constant). Centre `y` in shell `k >= 4`, side `l` in `[s_k / 32, s_k]`:
`(1/48) 65537^(-alpha/2) |Q| <= mu(Q) <= |Q|`. The ball of radius `l / 2`
about `y` lies in `Q` and has at least half its volume. -/
theorem lattice_shell_cube_mass {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {y : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖y‖) (h2 : ‖y‖ < (2:ℝ)^(k+1)) {l : ℝ}
    (hlo : Real.sqrt ((2:ℝ)^k) / 32 ≤ l) (hhi : l ≤ Real.sqrt ((2:ℝ)^k)) :
    ENNReal.ofReal ((1/48) * (65537:ℝ)^(-(α/2))) * volume (cube y l) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (cube y l) ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (cube y l) ≤ volume (cube y l) := by
  refine ⟨?_, lattice_mass_le_volume hα _⟩
  have hS := lattice_local_scale_ge hk
  have hin : ball y (l / 2) ⊆ cube y l :=
    ball_subset_closedBall.trans (cube_closedBall_subset y l)
  have hb := lattice_shell_ball_mass_lower hα hk h1 h2 (ρ := l / 2) (by linarith) (by linarith)
  calc ENNReal.ofReal ((1/48) * (65537:ℝ)^(-(α/2))) * volume (cube y l)
      ≤ ENNReal.ofReal ((1/48) * (65537:ℝ)^(-(α/2))) * (2 * volume (ball y (l / 2))) :=
        mul_le_mul_left' (lattice_shell_cube_volume_le y (by linarith)) _
    _ = ENNReal.ofReal ((1/24) * (65537:ℝ)^(-(α/2))) * volume (ball y (l / 2)) := by
        rw [← mul_assoc]
        congr 1
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ _ := hb.trans (measure_mono hin)

/-- **Cell mass, balls, with the constant of the cubes.** The statement of the
draft paragraph for a ball of radius `l` in `[s_k / 32, s_k]`:
`(1/48) 65537^(-alpha/2) |B| <= mu(B) <= |B|`. Weaker than
`lattice_shell_ball_mass`, which has `1/24`. -/
theorem lattice_shell_ball_mass_draft {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {x0 : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖x0‖) (h2 : ‖x0‖ < (2:ℝ)^(k+1)) {l : ℝ}
    (hlo : Real.sqrt ((2:ℝ)^k) / 32 ≤ l) (hhi : l ≤ Real.sqrt ((2:ℝ)^k)) :
    ENNReal.ofReal ((1/48) * (65537:ℝ)^(-(α/2))) * volume (ball x0 l) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 l) ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (ball x0 l) ≤ volume (ball x0 l) := by
  have hS := lattice_local_scale_ge hk
  have hq : (0:ℝ) < (65537:ℝ)^(-(α/2)) := by positivity
  refine ⟨le_trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (by linarith)) _)
    (lattice_shell_ball_mass_lower hα hk h1 h2 (by linarith) hhi), lattice_mass_le_volume hα _⟩

/-- **(G1) for the cells of the covering, with the same constant.** The
cells of the "Large balls" paragraph are the cubes of side `sigma(y) / 32`
centred at `y`. For `|y| >= 16` (centre in a shell `k >= 4`) the side lies in
`[s_k / 32, 0.045 s_k]`, so `lattice_shell_cube_mass` applies:
`(1/48) 65537^(-alpha/2) |Q| <= mu(Q) <= |Q|`. -/
theorem lattice_shell_covering_cell_mass {α : ℝ} (hα : 0 ≤ α) {y : LatticeSpace}
    (hy : 16 ≤ ‖y‖) :
    ENNReal.ofReal ((1/48) * (65537:ℝ)^(-(α/2))) *
        volume (cube y (Real.sqrt (1 + ‖y‖) / 32)) ≤
      (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (cube y (Real.sqrt (1 + ‖y‖) / 32)) ∧
    (volume.withDensity (fun x => ENNReal.ofReal (latticeWeight latticeValleys α x)))
        (cube y (Real.sqrt (1 + ‖y‖) / 32)) ≤
      volume (cube y (Real.sqrt (1 + ‖y‖) / 32)) := by
  obtain ⟨k, hk, h1, h2⟩ := lattice_local_shell_exists hy
  obtain ⟨ha, hb⟩ := lattice_dp_cell_side_range hk h1 h2
  have hS := lattice_local_scale_ge hk
  exact lattice_shell_cube_mass hα hk h1 h2 ha (by linarith)

/-! ### The doubling bound of line 931 -/

/-- `8 / ((1/24) 65537^(-alpha/2)) = 192 * 65537^(alpha/2)`. -/
theorem lattice_shell_const_doubling (α : ℝ) :
    8 / ((1/24) * (65537:ℝ)^(-(α/2))) = 192 * (65537:ℝ)^(α/2) := by
  have hpos : 0 < (65537:ℝ)^(α/2) := by positivity
  rw [Real.rpow_neg (by norm_num)]
  field_simp
  norm_num

/-- **Doubling from the cell mass.** Centre in shell `k >= 4`, radius in
`[s_k / 64, s_k]`: `mu(2B) <= |2B| = 8 |B| <= 192 * 65537^(alpha/2) mu(B)`. -/
theorem lattice_shell_ball_doubling {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 4 ≤ k)
    {x0 : LatticeSpace} (h1 : (2:ℝ)^k ≤ ‖x0‖) (h2 : ‖x0‖ < (2:ℝ)^(k+1)) {ρ : ℝ}
    (hlo : Real.sqrt ((2:ℝ)^k) / 64 ≤ ρ) (hhi : ρ ≤ Real.sqrt ((2:ℝ)^k)) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal (192 * (65537:ℝ)^(α/2))) x0 ρ := by
  have h := lattice_mass_double_of_lower hα x0 (c := (1/24) * (65537:ℝ)^(-(α/2)))
    (by positivity) (lattice_shell_ball_mass_lower hα hk h1 h2 hlo hhi)
  rw [lattice_shell_const_doubling] at h
  exact h

/-- **Paper, line 931, sharp form.** If `x_0` lies in a shell `k >= 4` (that
is, `|x_0| >= 16`) and `sigma_0 / 20 < rho <= sigma_0 / 10`, then
`mu(2B) <= 192 * 65537^(alpha/2) mu(B)`, that is, `192 / c_alpha` with
`c_alpha = 65537^(-alpha/2)`. -/
theorem lattice_line931_doubling_sharp {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hlo : Real.sqrt (1 + ‖x0‖) / 20 < ρ)
    (hhi : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal (192 * (65537:ℝ)^(α/2))) x0 ρ := by
  obtain ⟨k, hk, h1, h2⟩ := lattice_local_shell_exists hx0
  obtain ⟨ha, hb⟩ := lattice_small_mass_radius_range hk h1 h2 hlo hhi
  have hS := lattice_local_scale_ge hk
  exact lattice_shell_ball_doubling hα hk h1 h2 (by linarith) hb

/-- **Paper, line 931, with the constant of `(eq:cellmass)` as drafted**
(`(1/48) c_alpha` for cubes and balls alike): under the same hypotheses,
`mu(2B) <= 384 * 65537^(alpha/2) mu(B)`, that is, `384 / c_alpha`. Weaker
than `lattice_line931_doubling_sharp`. -/
theorem lattice_line931_doubling_draft {α : ℝ} (hα : 0 ≤ α) {x0 : LatticeSpace}
    (hx0 : 16 ≤ ‖x0‖) {ρ : ℝ} (hlo : Real.sqrt (1 + ‖x0‖) / 20 < ρ)
    (hhi : ρ ≤ Real.sqrt (1 + ‖x0‖) / 10) :
    doublingAt (volume : Measure LatticeSpace) (latticeWeight latticeValleys α)
      (ENNReal.ofReal (384 * (65537:ℝ)^(α/2))) x0 ρ := by
  have hq : (0:ℝ) < (65537:ℝ)^(α/2) := by positivity
  exact doublingAt_mono (ENNReal.ofReal_le_ofReal (by linarith))
    (lattice_line931_doubling_sharp hα hx0 hlo hhi)

/-! ### Two hand counterexamples of the first pass -/

/-- On the interval `(-1, 1)` the function `x` has variance at least `1/4`
about every constant, for Lebesgue measure: off the interval of length one
about `m` the square is at least `1/4`. -/
theorem transfer_counterexample_variance (m : ℝ) :
    ENNReal.ofReal (1/4) ≤
      ∫⁻ x in ball (0:ℝ) 1, ENNReal.ofReal ((x - m)^2) * ENNReal.ofReal 1 := by
  have hT : MeasurableSet (ball (0:ℝ) 1 \ ball m (1/2)) :=
    measurableSet_ball.diff measurableSet_ball
  have hvol : (1:ℝ≥0∞) ≤ volume (ball (0:ℝ) 1 \ ball m (1/2)) := by
    refine le_trans ?_ le_measure_diff
    rw [Real.volume_ball, Real.volume_ball, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  calc ENNReal.ofReal (1/4) = ENNReal.ofReal (1/4) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (1/4) * volume (ball (0:ℝ) 1 \ ball m (1/2)) :=
        mul_le_mul_left' hvol _
    _ = ∫⁻ _ in ball (0:ℝ) 1 \ ball m (1/2), ENNReal.ofReal (1/4) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in ball (0:ℝ) 1 \ ball m (1/2),
          ENNReal.ofReal ((x - m)^2) * ENNReal.ofReal 1 := by
        apply setLIntegral_mono' hT
        intro x hx
        rw [ENNReal.ofReal_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        have h2 : ¬ dist x m < 1/2 := fun h => hx.2 (mem_ball.mpr h)
        rw [Real.dist_eq] at h2
        have h3 : 1/2 ≤ |x - m| := not_lt.mp h2
        nlinarith [sq_abs (x - m), abs_nonneg (x - m)]
    _ ≤ _ := lintegral_mono_set diff_subset

/-- **`poincareAt_transfer_local` is false without `1 <= lam`.** On the real
line take `lam = 0`, `w = 0`, `v = 1`, `c = C = P = 1`, the ball `B(0, 1)`.
The comparison of the weights on `ball a (lam * r)`, which is empty, holds;
the Poincare inequality for `w = 0` holds; the Poincare inequality for
`v = 1` with the constant `C * P / c` fails, its right side being an energy
over the empty set. -/
theorem poincareAt_transfer_local_fails_lam_zero :
    (∀ x ∈ ball (0:ℝ) (0 * 1), (1:ℝ≥0∞) * ENNReal.ofReal ((fun _ : ℝ => (0:ℝ)) x) ≤
        ENNReal.ofReal ((fun _ : ℝ => (1:ℝ)) x)) ∧
    (∀ x ∈ ball (0:ℝ) (0 * 1), ENNReal.ofReal ((fun _ : ℝ => (1:ℝ)) x) ≤
        (1:ℝ≥0∞) * ENNReal.ofReal ((fun _ : ℝ => (0:ℝ)) x)) ∧
    poincareAt (volume : Measure ℝ) (fun _ => 0) 1 0 0 1 ∧
    ¬ poincareAt (volume : Measure ℝ) (fun _ => 1) (1 * 1 / 1) 0 0 1 := by
  have hempty : ball (0:ℝ) (0 * 1) = ∅ := by rw [zero_mul, ball_zero]
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun u _ => ?_, fun h => ?_⟩
  · rw [hempty] at hx
    exact absurd hx (notMem_empty x)
  · rw [hempty] at hx
    exact absurd hx (notMem_empty x)
  · have h0 : weightedVariance ((volume : Measure ℝ).restrict (ball 0 1))
        (fun _ => ENNReal.ofReal 0) u = 0 := by
      unfold weightedVariance
      simp
    rw [h0]
    exact zero_le _
  · have h1 := h (fun x => x) contDiffOn_id
    have h0 : weightedEnergy ((volume : Measure ℝ).restrict (ball 0 (0 * 1)))
        (fun _ => ENNReal.ofReal 1) (fun x => x) = 0 := by
      unfold weightedEnergy
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    rw [h0, mul_zero] at h1
    have h2 : ENNReal.ofReal (1/4) ≤ weightedVariance
        ((volume : Measure ℝ).restrict (ball 0 1)) (fun _ => ENNReal.ofReal 1) (fun x => x) :=
      le_iInf fun m => transfer_counterexample_variance m
    have h3 : (0:ℝ≥0∞) < ENNReal.ofReal (1/4) := ENNReal.ofReal_pos.mpr (by norm_num)
    exact absurd (h2.trans h1) (not_le.mpr h3)

/-- **A partition of unity across an overlap of length `q - p`.** Let `psi1`
vanish to the right of `q` and `psi2` to the left of `p`, `p < q`, and let
`psi1 + psi2 = 1` at `p`. Then `psi1` falls from `1` at `p` to `0` at `q`, so
its derivative equals `-1 / (q - p)` at some point of the overlap `(p, q)`. -/
theorem partition_overlap_derivative {p q : ℝ} (hpq : p < q) {psi1 psi2 : ℝ → ℝ}
    (hd : Differentiable ℝ psi1) (hc : Continuous psi2)
    (h1 : ∀ x, q < x → psi1 x = 0) (h2 : ∀ x, x < p → psi2 x = 0)
    (hsum : psi1 p + psi2 p = 1) :
    ∃ x ∈ Ioo p q, deriv psi1 x = -(1 / (q - p)) := by
  have hq : psi1 q = 0 := by
    have hcl : IsClosed {x | psi1 x = 0} := isClosed_eq hd.continuous continuous_const
    have hsub : closure (Ioi q) ⊆ {x | psi1 x = 0} :=
      hcl.closure_subset_iff.mpr (fun x hx => h1 x hx)
    exact hsub (by rw [closure_Ioi]; exact left_mem_Ici)
  have hp : psi2 p = 0 := by
    have hcl : IsClosed {x | psi2 x = 0} := isClosed_eq hc continuous_const
    have hsub : closure (Iio p) ⊆ {x | psi2 x = 0} :=
      hcl.closure_subset_iff.mpr (fun x hx => h2 x hx)
    exact hsub (by rw [closure_Iio]; exact right_mem_Iic)
  obtain ⟨x, hx, hder⟩ := exists_deriv_eq_slope psi1 hpq hd.continuous.continuousOn
    hd.differentiableOn
  refine ⟨x, hx, ?_⟩
  rw [hder, hq, show psi1 p = 1 by linarith]
  ring

/-- **The gradient bound of a partition of unity cannot hold on the enlarged
cubes** (one-dimensional form). For every `K` there are two closed unit
intervals with disjoint interiors, `Q_1 = [-1/2, 1/2]` and
`Q_2 = [c - 1/2, c + 1/2]` with `c >= 1`, such that every pair `psi1`, `psi2`
that vanishes outside the `1.01`-fold enlargements `Q_1^*`, `Q_2^*` and has
`psi1 + psi2 = 1` on the union of the open enlarged intervals has
`|psi1'| > K` at some point of `Q_1^* ∩ Q_2^*`. The sides are `1`, so no
bound `|psi_j'| <= K / s_j` holds on the enlarged intervals with `K`
independent of the family, for a partition that sums to one there. The proof
of `lem:glue` needs the sum to be one, and the bound, only on the union of
the cubes `Q_j` themselves, where both hold (`CubePartition`). -/
theorem partition_gradient_unbounded_on_enlarged (K : ℝ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ psi1 psi2 : ℝ → ℝ, Differentiable ℝ psi1 → Continuous psi2 →
      (∀ x, 101 / 100 / 2 < |x| → psi1 x = 0) →
      (∀ x, 101 / 100 / 2 < |x - c| → psi2 x = 0) →
      (∀ x, |x| < 101 / 100 / 2 ∨ |x - c| < 101 / 100 / 2 → psi1 x + psi2 x = 1) →
      ∃ x, |x| ≤ 101 / 100 / 2 ∧ |x - c| ≤ 101 / 100 / 2 ∧ K < |deriv psi1 x| := by
  have he : 0 < 1 / (|K| + 100) := by positivity
  have he' : 1 / (|K| + 100) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [abs_nonneg K])
  refine ⟨101 / 100 - 1 / (|K| + 100), by linarith, ?_⟩
  intro psi1 psi2 hd hc h1 h2 hsum
  obtain ⟨x, hx, hder⟩ := partition_overlap_derivative
    (p := 101 / 100 / 2 - 1 / (|K| + 100)) (q := 101 / 100 / 2) (by linarith) hd hc
    (fun x hx => h1 x (lt_of_lt_of_le hx (le_abs_self x)))
    (fun x hx => h2 x (by rw [abs_of_neg (by linarith)]; linarith))
    (hsum _ (Or.inl (by rw [abs_of_nonneg (by linarith)]; linarith)))
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (by linarith [hx.1])]
    exact hx.2.le
  · rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  · rw [hder, abs_neg, show 101 / 100 / 2 - (101 / 100 / 2 - 1 / (|K| + 100)) =
      1 / (|K| + 100) by ring, one_div_one_div, abs_of_pos (by positivity)]
    linarith [le_abs_self K]

end BrownRadial
