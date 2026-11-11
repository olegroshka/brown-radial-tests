import DoublingPoincare
import CubePartition

/-!
# The gluing lemma (`lem:glue` of the paper)

A Poincare inequality on a ball `B = ball x0 ρ`, with the energy over `4B`,
assembled from Poincare inequalities on balls `B_j` around the cubes of a
finite covering of the closed ball `2B`, by comparison with a reference
weight that satisfies the Poincare inequality on `2B`.

Setting. `μ` has the continuous nonnegative density `w` and `ν` the continuous
density `v`, both against Lebesgue measure on `EuclideanSpace ℝ (Fin n)`. The
cubes are `cube (c j) (s j)`, their enlargements `cube (c j) (κ * s j)` for
any `κ > 1` (the paper takes `1.01`), the relation `i ∼ j` is
`cubeNeighbor κ c s i j`, and `B_j = ball (b j) (R j)`.

Main statements, each with a finite constant `K` chosen before the family of
cubes, the ball, the weights and the test function:

* `gluing_lemma`: the paper's proof. Cell constants are the `μ`-means of `u`
  on the cubes. (G2) enters as the Poincare inequality on each `B_j` and as
  (G2b), `μ (B_j) ≤ Kb * μ (Q_j)`.
* `gluing_ball_le_cube_of_doubling`: (G2b) from doubling at balls centred in
  `B_j` with radius at most that of `B_j`.
* `gluing_lemma_of_local_doubling`: the two combined, the lemma as the paper
  states it.
* `gluing_lemma_without_doubling`: the same conclusion without any doubling
  hypothesis, taking the cell constants to be the means on the balls `B_j`.
  Not the paper's proof.
* `gluing_core`: the part of the argument common to both (steps 1, 3, 4, 6 of
  the paper's proof), with the cell constants and the two estimates of steps
  2 and 5 as hypotheses.

What the proof uses of the reference weight: the Poincare inequality at the
single ball `2B`, energy over `2B`. Doubling of `ν` is not used.

All integrals are lower Lebesgue integrals with values in `ℝ≥0∞`, and the
variance is the variational one (infimum over constants), so no
integrability has to be tracked. In dimension zero the statement is trivial
and is treated separately, because there `sqrt n * s j ≤ ρ` says nothing
about the sides.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal ContDiff Topology
namespace BrownRadial

universe u

/-! ## Scalar inequalities in the extended nonnegative reals -/

/-- Transport of `p ≤ 2 q + 2 r` between nonnegative reals. -/
theorem gluing_ofReal_le_two_add {p q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p ≤ 2 * q + 2 * r) :
    ENNReal.ofReal p ≤ 2 * ENNReal.ofReal q + 2 * ENNReal.ofReal r := by
  have e : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [e, ← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- `(x - z)² ≤ 2 (x - y)² + 2 (y - z)²`. -/
theorem gluing_ofReal_sq_sub_le (x y z : ℝ) :
    ENNReal.ofReal ((x - z) ^ 2) ≤
      2 * ENNReal.ofReal ((x - y) ^ 2) + 2 * ENNReal.ofReal ((y - z) ^ 2) :=
  gluing_ofReal_le_two_add (sq_nonneg _) (sq_nonneg _)
    (by nlinarith [sq_nonneg (x - y - (y - z))])

/-- `(x - z)² ≤ 2 (y - x)² + 2 (y - z)²`. -/
theorem gluing_ofReal_sq_sub_le_mid (x y z : ℝ) :
    ENNReal.ofReal ((x - z) ^ 2) ≤
      2 * ENNReal.ofReal ((y - x) ^ 2) + 2 * ENNReal.ofReal ((y - z) ^ 2) :=
  gluing_ofReal_le_two_add (sq_nonneg _) (sq_nonneg _)
    (by nlinarith [sq_nonneg (y - x + (y - z))])

/-- If `|t|` is at most a sum of at most `M` absolute values, then `t²` is at
most `M` times the sum of the squares. -/
theorem gluing_ofReal_sq_le_card_sum {ι : Type*} (T : Finset ι) {M : ℕ} (hM : T.card ≤ M)
    (t : ℝ) (f : ι → ℝ) (ht : |t| ≤ ∑ i ∈ T, |f i|) :
    ENNReal.ofReal (t ^ 2) ≤ M * ∑ i ∈ T, ENNReal.ofReal ((f i) ^ 2) := by
  have h1 : t ^ 2 ≤ (∑ i ∈ T, |f i|) ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have h2 : (∑ i ∈ T, |f i|) ^ 2 ≤ T.card * ∑ i ∈ T, |f i| ^ 2 := sq_sum_le_card_mul_sum_sq
  have h3 : (0 : ℝ) ≤ ∑ i ∈ T, (f i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h4 : t ^ 2 ≤ M * ∑ i ∈ T, (f i) ^ 2 := by
    refine h1.trans (h2.trans ?_)
    simp only [sq_abs]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM) h3
  calc ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (M * ∑ i ∈ T, (f i) ^ 2) :=
        ENNReal.ofReal_le_ofReal h4
    _ = M * ∑ i ∈ T, ENNReal.ofReal ((f i) ^ 2) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]

/-! ## Sums of integrals over a covering -/

section Covering

variable {X : Type*} [MeasurableSpace X]

/-- The integral over a set covered by finitely many sets is at most the sum
of the integrals over those sets. No measurability is needed. -/
theorem gluing_lintegral_le_sum_cover (μ : Measure X) {ι : Type*} [Fintype ι] (A : ι → Set X)
    {S : Set X} (hS : S ⊆ ⋃ j, A j) (f : X → ℝ≥0∞) :
    ∫⁻ x in S, f x ∂μ ≤ ∑ j, ∫⁻ x in A j, f x ∂μ :=
  (lintegral_mono_set hS).trans ((lintegral_iUnion_le A f).trans_eq (tsum_fintype _))

/-- The same, keeping only a set of indices that contains every index whose
set meets `S`. -/
theorem gluing_lintegral_le_sum_meeting (μ : Measure X) {ι : Type*} [Fintype ι]
    (A : ι → Set X) {S : Set X} (hS : S ⊆ ⋃ j, A j) (f : X → ℝ≥0∞) (J : Finset ι)
    (hJ : ∀ j, (A j ∩ S).Nonempty → j ∈ J) :
    ∫⁻ x in S, f x ∂μ ≤ ∑ j ∈ J, ∫⁻ x in A j, f x ∂μ := by
  classical
  have h1 : S ⊆ ⋃ j, (if j ∈ J then A j else ∅) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hS hx)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [if_pos (hJ j ⟨x, hj, hx⟩)]
    exact hj
  refine (gluing_lintegral_le_sum_cover μ _ h1 f).trans (le_of_eq ?_)
  have h2 : ∑ j, ∫⁻ x in (if j ∈ J then A j else ∅), f x ∂μ =
      ∑ j ∈ J, ∫⁻ x in (if j ∈ J then A j else ∅), f x ∂μ := by
    symm
    refine Finset.sum_subset (Finset.subset_univ J) fun j _ hj => ?_
    rw [if_neg hj]
    simp
  rw [h2]
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos hj]

/-- Bounded overlap: if no point lies in more than `N` of the sets `A i`, and
those with index in `J` lie in `S`, the integrals over them add up to at most
`N` times the integral over `S`. No measurability of the integrand is needed. -/
theorem gluing_sum_lintegral_le_of_overlap (μ : Measure X) {ι : Type*} (J : Finset ι)
    (A : ι → Set X) (hA : ∀ i ∈ J, MeasurableSet (A i)) {S : Set X} (hSm : MeasurableSet S)
    (hS : ∀ i ∈ J, A i ⊆ S) (N : ℕ)
    (hN : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ A i) → T.card ≤ N) (f : X → ℝ≥0∞) :
    ∑ i ∈ J, ∫⁻ x in A i, f x ∂μ ≤ N * ∫⁻ x in S, f x ∂μ := by
  classical
  have hmeas : ∑ i ∈ J, μ.restrict (A i) ≤ (N : ℝ≥0∞) • μ.restrict S := by
    rw [Measure.le_iff]
    intro t ht
    rw [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht]
    have h1 : ∑ i ∈ J, μ.restrict (A i) t =
        ∫⁻ y, ∑ i ∈ J, (t ∩ A i).indicator (1 : X → ℝ≥0∞) y ∂μ := by
      rw [lintegral_finset_sum J fun i hi => measurable_one.indicator (ht.inter (hA i hi))]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Measure.restrict_apply ht, lintegral_indicator_one (ht.inter (hA i hi))]
    rw [h1, ← lintegral_indicator_const (ht.inter hSm)]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ t ∩ S
    · rw [indicator_of_mem hy]
      have h2 : ∑ i ∈ J, (t ∩ A i).indicator (1 : X → ℝ≥0∞) y =
          ((J.filter fun i => y ∈ t ∩ A i).card : ℝ≥0∞) := by
        simp [indicator_apply, Finset.sum_boole]
      rw [h2]
      have h3 := hN y (J.filter fun i => y ∈ t ∩ A i)
        (fun i hi => ((Finset.mem_filter.mp hi).2).2)
      exact_mod_cast h3
    · rw [indicator_of_notMem hy]
      refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
      exact indicator_of_notMem (fun h => hy ⟨h.1, hS i hi h.2⟩) _
  calc ∑ i ∈ J, ∫⁻ x in A i, f x ∂μ
      = ∫⁻ x, f x ∂(∑ i ∈ J, μ.restrict (A i)) := (lintegral_finset_sum_measure J f _).symm
    _ ≤ ∫⁻ x, f x ∂((N : ℝ≥0∞) • μ.restrict S) := lintegral_mono' hmeas le_rfl
    _ = N * ∫⁻ x in S, f x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]

end Covering

/-! ## Counting over neighbours -/

/-- With a symmetric neighbour relation and at most `M` neighbours each, the
double sum of `e i + e j` over neighbouring pairs is at most `2 M` times the
sum of `e`. -/
theorem gluing_sum_neighbors_le {ι : Type*} [Fintype ι] (Nbr : ι → Finset ι)
    (hsym : ∀ i j, i ∈ Nbr j → j ∈ Nbr i) {M : ℕ} (hM : ∀ j, (Nbr j).card ≤ M)
    (e : ι → ℝ≥0∞) :
    ∑ j, ∑ i ∈ Nbr j, (e i + e j) ≤ 2 * M * ∑ j, e j := by
  have h1 : ∑ j, ∑ i ∈ Nbr j, e j ≤ M * ∑ j, e j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_right' (by exact_mod_cast hM j) _
  have h2 : ∑ j, ∑ i ∈ Nbr j, e i = ∑ i, ∑ j ∈ Nbr i, e i := by
    refine Finset.sum_comm' fun j i => ?_
    simp only [Finset.mem_univ, true_and, and_true]
    exact ⟨hsym i j, hsym j i⟩
  simp only [Finset.sum_add_distrib]
  rw [h2]
  calc ∑ i, ∑ _j ∈ Nbr i, e i + ∑ j, ∑ _i ∈ Nbr j, e j ≤ M * ∑ j, e j + M * ∑ j, e j :=
        add_le_add h1 h1
    _ = 2 * M * ∑ j, e j := by ring

/-! ## The bookkeeping of the proof, with the integrals replaced by numbers -/

/-- The three double sums over neighbouring pairs, bounded by the sum of the
energies over the balls. Here `F i j` stands for the integral of
`(u - a i)²` over the cube `j`, `D i j` for `(a i - a j)²`, `σ j` for the
squared side and `τ j` for the gradient constant over the squared side. -/
theorem gluing_assembly_pairs {ι : Type*} [Fintype ι] (Nbr : ι → Finset ι)
    (hsym : ∀ i j, i ∈ Nbr j → j ∈ Nbr i) {M : ℕ} (hM : ∀ j, (Nbr j).card ≤ M)
    (muQ Eb σ τ : ι → ℝ≥0∞) (F D : ι → ι → ℝ≥0∞) {r2 k2 A En : ℝ≥0∞} {Nb : ℕ}
    (hσ : ∀ j, σ j ≤ r2) (hτσ : ∀ j, τ j * σ j ≤ k2)
    (hF : ∀ j, ∀ i ∈ Nbr j, F i j ≤ A * σ j * Eb i)
    (hD : ∀ j, ∀ i ∈ Nbr j, muQ j * D i j ≤ A * σ j * (Eb i + Eb j))
    (hEb : ∑ j, Eb j ≤ Nb * En) :
    ∑ j, ∑ i ∈ Nbr j, F i j ≤ A * r2 * (2 * M * (Nb * En)) ∧
    ∑ j, (∑ i ∈ Nbr j, D i j) * muQ j ≤ A * r2 * (2 * M * (Nb * En)) ∧
    ∑ j, τ j * ((∑ i ∈ Nbr j, D i j) * muQ j) ≤ A * k2 * (2 * M * (Nb * En)) := by
  have hS : ∑ j, ∑ i ∈ Nbr j, (Eb i + Eb j) ≤ 2 * M * (Nb * En) :=
    (gluing_sum_neighbors_le Nbr hsym hM Eb).trans (mul_le_mul_left' hEb _)
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ (mul_le_mul_left' hS _)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    calc F i j ≤ A * σ j * Eb i := hF j i hi
      _ ≤ A * r2 * (Eb i + Eb j) := mul_le_mul' (mul_le_mul_left' (hσ j) A) le_self_add
  · refine le_trans ?_ (mul_le_mul_left' hS _)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    calc D i j * muQ j = muQ j * D i j := mul_comm _ _
      _ ≤ A * σ j * (Eb i + Eb j) := hD j i hi
      _ ≤ A * r2 * (Eb i + Eb j) := mul_le_mul_right' (mul_le_mul_left' (hσ j) A) _
  · refine le_trans ?_ (mul_le_mul_left' hS _)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    calc τ j * (D i j * muQ j) = τ j * (muQ j * D i j) := by rw [mul_comm (D i j)]
      _ ≤ τ j * (A * σ j * (Eb i + Eb j)) := mul_le_mul_left' (hD j i hi) _
      _ = A * (τ j * σ j) * (Eb i + Eb j) := by ring
      _ ≤ A * k2 * (Eb i + Eb j) := mul_le_mul_right' (mul_le_mul_left' (hτσ j) A) _

/-- The chain of the proof for the cube terms that depend on the centring
constant: after the comparison of the two measures on cubes, they are
controlled by the squared deviation of the glued function from the constant
and by the pair sums. `d j` stands for `(a j - m)²` and `Uj j` for the integral
of `(U - m)²` over the cube `j` against the reference weight. -/
theorem gluing_assembly_centering {ι : Type*} [Fintype ι] (Nbr : ι → Finset ι) {M : ℕ}
    (J1 : Finset ι) (muQ nuQ : ι → ℝ≥0∞) (D : ι → ι → ℝ≥0∞) {T2 G : ℝ≥0∞} {N0 : ℕ}
    (hT2 : ∑ j, (∑ i ∈ Nbr j, D i j) * muQ j ≤ T2)
    (hG1 : ∀ j, muQ j ≤ G * nuQ j) (hG2 : ∀ j, nuQ j ≤ G * muQ j)
    (d Uj : ι → ℝ≥0∞) {Vm : ℝ≥0∞}
    (h5 : ∀ j, nuQ j * d j ≤ 2 * Uj j + 2 * (M * ∑ i ∈ Nbr j, D i j) * nuQ j)
    (h7 : ∑ j ∈ J1, Uj j ≤ N0 * Vm) :
    ∑ j ∈ J1, d j * muQ j ≤ 2 * G * (N0 * Vm) + 2 * M * G ^ 2 * T2 := by
  have hnu : ∑ j ∈ J1, (∑ i ∈ Nbr j, D i j) * nuQ j ≤ G * T2 := by
    calc ∑ j ∈ J1, (∑ i ∈ Nbr j, D i j) * nuQ j
        ≤ ∑ j, (∑ i ∈ Nbr j, D i j) * nuQ j :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ J1)
      _ ≤ ∑ j, G * ((∑ i ∈ Nbr j, D i j) * muQ j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc (∑ i ∈ Nbr j, D i j) * nuQ j ≤ (∑ i ∈ Nbr j, D i j) * (G * muQ j) :=
                mul_le_mul_left' (hG2 j) _
            _ = G * ((∑ i ∈ Nbr j, D i j) * muQ j) := by ring
      _ = G * ∑ j, (∑ i ∈ Nbr j, D i j) * muQ j := by rw [Finset.mul_sum]
      _ ≤ G * T2 := mul_le_mul_left' hT2 G
  calc ∑ j ∈ J1, d j * muQ j
      ≤ ∑ j ∈ J1, (2 * G * Uj j + 2 * M * G * ((∑ i ∈ Nbr j, D i j) * nuQ j)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc d j * muQ j ≤ d j * (G * nuQ j) := mul_le_mul_left' (hG1 j) _
          _ = G * (nuQ j * d j) := by ring
          _ ≤ G * (2 * Uj j + 2 * (M * ∑ i ∈ Nbr j, D i j) * nuQ j) :=
              mul_le_mul_left' (h5 j) G
          _ = 2 * G * Uj j + 2 * M * G * ((∑ i ∈ Nbr j, D i j) * nuQ j) := by ring
    _ = 2 * G * ∑ j ∈ J1, Uj j + 2 * M * G * ∑ j ∈ J1, (∑ i ∈ Nbr j, D i j) * nuQ j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * G * (N0 * Vm) + 2 * M * G * (G * T2) :=
        add_le_add (mul_le_mul_left' h7 _) (mul_le_mul_left' hnu _)
    _ = 2 * G * (N0 * Vm) + 2 * M * G ^ 2 * T2 := by ring

/-- The whole chain with the integrals replaced by numbers. `L m` is the
integral of `(u - m)²` over the ball, `Lj j m` the same over the cube `j`,
`Vm m` the integral of `(U - m)²` over the doubled ball against the reference
weight, `EnU` the energy of `U` there. -/
theorem gluing_assembly {ι : Type*} [Fintype ι] (Nbr : ι → Finset ι) {M : ℕ} (J1 : Finset ι)
    (muQ nuQ τ : ι → ℝ≥0∞) (F D : ι → ι → ℝ≥0∞) {r2 T1 T2 T3 G EnU Pν : ℝ≥0∞} {N0 : ℕ}
    (hGtop : G ≠ ⊤)
    (hT1 : ∑ j, ∑ i ∈ Nbr j, F i j ≤ T1)
    (hT2 : ∑ j, (∑ i ∈ Nbr j, D i j) * muQ j ≤ T2)
    (hT3 : ∑ j, τ j * ((∑ i ∈ Nbr j, D i j) * muQ j) ≤ T3)
    (hG1 : ∀ j, muQ j ≤ G * nuQ j) (hG2 : ∀ j, nuQ j ≤ G * muQ j)
    (L Vm : ℝ → ℝ≥0∞) (d Lj Uj : ι → ℝ → ℝ≥0∞)
    (h0 : ∀ m, L m ≤ ∑ j ∈ J1, Lj j m)
    (h4 : ∀ m, ∀ j ∈ J1, Lj j m ≤ 2 * (M * ∑ i ∈ Nbr j, F i j) +
      (4 * d j m + 4 * (M * ∑ i ∈ Nbr j, D i j)) * muQ j)
    (h5 : ∀ m j, nuQ j * d j m ≤ 2 * Uj j m + 2 * (M * ∑ i ∈ Nbr j, D i j) * nuQ j)
    (h7 : ∀ m, ∑ j ∈ J1, Uj j m ≤ N0 * Vm m)
    (h8 : ⨅ m, Vm m ≤ Pν * (4 * r2) * EnU)
    (h9 : EnU ≤ ∑ j, τ j * ((∑ i ∈ Nbr j, D i j) * nuQ j)) :
    ⨅ m, L m ≤ 2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2 +
      32 * G ^ 2 * N0 * Pν * r2 * T3 := by
  have hEnU : EnU ≤ G * T3 := by
    calc EnU ≤ ∑ j, τ j * ((∑ i ∈ Nbr j, D i j) * nuQ j) := h9
      _ ≤ ∑ j, G * (τ j * ((∑ i ∈ Nbr j, D i j) * muQ j)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc τ j * ((∑ i ∈ Nbr j, D i j) * nuQ j)
              ≤ τ j * ((∑ i ∈ Nbr j, D i j) * (G * muQ j)) :=
                mul_le_mul_left' (mul_le_mul_left' (hG2 j) _) _
            _ = G * (τ j * ((∑ i ∈ Nbr j, D i j) * muQ j)) := by ring
      _ = G * ∑ j, τ j * ((∑ i ∈ Nbr j, D i j) * muQ j) := by rw [Finset.mul_sum]
      _ ≤ G * T3 := mul_le_mul_left' hT3 G
  have hm : ∀ m, L m ≤ (2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2) + 8 * G * N0 * Vm m := by
    intro m
    have hd := gluing_assembly_centering Nbr (M := M) J1 muQ nuQ D hT2 hG1 hG2
      (fun j => d j m) (fun j => Uj j m) (h5 m) (h7 m)
    have hF1 : ∑ j ∈ J1, ∑ i ∈ Nbr j, F i j ≤ T1 :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ J1)).trans hT1
    have hD1 : ∑ j ∈ J1, (∑ i ∈ Nbr j, D i j) * muQ j ≤ T2 :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ J1)).trans hT2
    calc L m ≤ ∑ j ∈ J1, Lj j m := h0 m
      _ ≤ ∑ j ∈ J1, (2 * (M * ∑ i ∈ Nbr j, F i j) +
            (4 * d j m + 4 * (M * ∑ i ∈ Nbr j, D i j)) * muQ j) := Finset.sum_le_sum (h4 m)
      _ = 2 * M * ∑ j ∈ J1, ∑ i ∈ Nbr j, F i j + 4 * ∑ j ∈ J1, d j m * muQ j +
            4 * M * ∑ j ∈ J1, (∑ i ∈ Nbr j, D i j) * muQ j := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 2 * M * T1 + 4 * (2 * G * (N0 * Vm m) + 2 * M * G ^ 2 * T2) + 4 * M * T2 :=
          add_le_add (add_le_add (mul_le_mul_left' hF1 _) (mul_le_mul_left' hd _))
            (mul_le_mul_left' hD1 _)
      _ = (2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2) + 8 * G * N0 * Vm m := by ring
  have hc : (8 : ℝ≥0∞) * G * N0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hGtop) (ENNReal.natCast_ne_top N0)
  calc ⨅ m, L m
      ≤ ⨅ m, ((2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2) + 8 * G * N0 * Vm m) := iInf_mono hm
    _ = (2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2) + 8 * G * N0 * ⨅ m, Vm m := by
        rw [ENNReal.mul_iInf (fun h => absurd h hc), ENNReal.add_iInf]
    _ ≤ (2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2) +
          8 * G * N0 * (Pν * (4 * r2) * (G * T3)) :=
        add_le_add le_rfl (mul_le_mul_left' (h8.trans (mul_le_mul_left' hEnU _)) _)
    _ = 2 * M * T1 + (4 * M + 8 * M * G ^ 2) * T2 + 32 * G ^ 2 * N0 * Pν * r2 * T3 := by ring

/-! ## Means and minimizers -/

/-- The weighted integral of a squared deviation, as the real integral
against the measure with density. -/
theorem gluing_lintegral_sq_eq_ofReal {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w : X → ℝ≥0∞} {u : X → ℝ} (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)]
    (hi : Integrable u (μ.withDensity w))
    (hi2 : Integrable (fun x => (u x) ^ 2) (μ.withDensity w)) (m : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((u x - m) ^ 2) * w x ∂μ =
      ENNReal.ofReal (∫ x, (u x - m) ^ 2 ∂μ.withDensity w) := by
  have hi' := integrable_centered_square _ hi hi2 m
  rw [ofReal_integral_eq_lintegral_ofReal hi'
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    lintegral_withDensity_eq_lintegral_mul₀' hw
      hi'.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  simp only [Pi.mul_apply, mul_comm]

section Cube

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The variational variance on a ball is attained (at the weighted mean). -/
theorem gluing_variance_ball_attained {w u : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {a : E} {r : ℝ} (hu : ContinuousOn u (closedBall a r)) :
    ∃ m : ℝ, ∫⁻ x in ball a r, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) =
      weightedVariance (volume.restrict (ball a r)) (fun x => ENNReal.ofReal (w x)) u := by
  haveI := weighted_ball_finite (volume : Measure E) hw a r
  have hi := continuousOn_weighted_ball_integrable (volume : Measure E) hw hw0 hu
  have hi2 := continuousOn_weighted_ball_integrable (volume : Measure E) hw hw0 (hu.pow 2)
  have hwm : AEMeasurable (fun x => ENNReal.ofReal (w x)) (volume.restrict (ball a r)) :=
    hw.measurable.ennreal_ofReal.aemeasurable
  refine ⟨⨍ y, u y ∂(volume.restrict (ball a r)).withDensity (fun x => ENNReal.ofReal (w x)), ?_⟩
  rw [weightedVariance_eq_mean_ae _ hwm hi hi2]
  exact gluing_lintegral_sq_eq_ofReal _ hwm hi hi2 _

/-- A Poincare inequality at a ball, with a centring constant made explicit. -/
theorem gluing_ball_minimizer {w u : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {P : ℝ≥0∞} {a : E} {r : ℝ} (hP : poincareAt volume w P 1 a r)
    (hu : ContDiffOn ℝ 1 u (closedBall a r)) :
    ∃ m : ℝ, ∫⁻ x in ball a r, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) ≤
      P * ENNReal.ofReal (r ^ 2) *
        ∫⁻ x in ball a r, ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x) := by
  obtain ⟨m, hm⟩ := gluing_variance_ball_attained hw hw0 hu.continuousOn
  refine ⟨m, ?_⟩
  rw [hm]
  have h := hP u (by rwa [one_mul])
  rw [one_mul] at h
  exact h

/-- Cubes are compact. -/
theorem gluing_cube_isCompact (c : E) (s : ℝ) : IsCompact (cube c s) :=
  Metric.isCompact_of_isClosed_isBounded (cube_isClosed c s)
    (isBounded_closedBall.subset (cube_subset_closedBall c s))

/-- The weighted mean on a compact set: its squared distance to any constant,
times the mass, is at most the integral of the squared deviation from that
constant. -/
theorem gluing_compact_mean_sq_le {w u : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {Q : Set E} (hQ : IsCompact Q) (hu : ContinuousOn u Q) (m : ℝ) :
    (∫⁻ x in Q, ENNReal.ofReal (w x)) *
        ENNReal.ofReal ((⨍ y, u y ∂(volume.restrict Q).withDensity
          (fun x => ENNReal.ofReal (w x)) - m) ^ 2) ≤
      ∫⁻ x in Q, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) := by
  haveI : IsFiniteMeasure ((volume.restrict Q).withDensity (fun x => ENNReal.ofReal (w x))) := by
    apply isFiniteMeasure_withDensity_ofReal
    exact (hw.continuousOn.integrableOn_compact hQ).hasFiniteIntegral
  have hint : ∀ g : E → ℝ, ContinuousOn g Q →
      Integrable g ((volume.restrict Q).withDensity (fun x => ENNReal.ofReal (w x))) := by
    intro g hg
    apply (integrable_withDensity_iff_integrable_smul' hw.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
    exact (hw.continuousOn.mul hg).integrableOn_compact hQ
  have hi := hint u hu
  have hi2 : Integrable (fun x => (u x) ^ 2)
      ((volume.restrict Q).withDensity (fun x => ENNReal.ofReal (w x))) := hint _ (hu.pow 2)
  have hwm : AEMeasurable (fun x => ENNReal.ofReal (w x)) (volume.restrict Q) :=
    hw.measurable.ennreal_ofReal.aemeasurable
  have hid := centered_square_identity _ hi hi2 m
  have hnn : 0 ≤ ∫ x, (u x - ⨍ y, u y ∂(volume.restrict Q).withDensity
      (fun x => ENNReal.ofReal (w x))) ^ 2 ∂(volume.restrict Q).withDensity
      (fun x => ENNReal.ofReal (w x)) := integral_nonneg fun x => sq_nonneg _
  have hmass : ∫⁻ x in Q, ENNReal.ofReal (w x) =
      ((volume.restrict Q).withDensity (fun x => ENNReal.ofReal (w x))) univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [gluing_lintegral_sq_eq_ofReal _ hwm hi hi2 m, hmass]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal (le_of_add_le_of_nonneg_right
    (le_of_eq hid.symm) hnn))
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Measurability of the integrands, on a set where `u` is continuous. -/
theorem gluing_aemeasurable_sq_mul {Q : Set E} (hQ : MeasurableSet Q) {w u : E → ℝ}
    (hw : Continuous w) (hu : ContinuousOn u Q) (p : ℝ) :
    AEMeasurable (fun x => ENNReal.ofReal ((u x - p) ^ 2) * ENNReal.ofReal (w x))
      (volume.restrict Q) :=
  ((((hu.sub continuousOn_const).pow 2).aemeasurable hQ).ennreal_ofReal).mul
    hw.measurable.ennreal_ofReal.aemeasurable

/-- Two constants compared through a function on a set: the mass times the
squared difference is at most twice the sum of the two squared deviations. -/
theorem gluing_cube_diff_le {Q : Set E} (hQ : MeasurableSet Q) {w u : E → ℝ}
    (hw : Continuous w) (hu : ContinuousOn u Q) (p q : ℝ) :
    (∫⁻ x in Q, ENNReal.ofReal (w x)) * ENNReal.ofReal ((p - q) ^ 2) ≤
      2 * (∫⁻ x in Q, ENNReal.ofReal ((u x - p) ^ 2) * ENNReal.ofReal (w x)) +
      2 * ∫⁻ x in Q, ENNReal.ofReal ((u x - q) ^ 2) * ENNReal.ofReal (w x) := by
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  calc (∫⁻ x in Q, ENNReal.ofReal (w x)) * ENNReal.ofReal ((p - q) ^ 2)
      = ∫⁻ x in Q, ENNReal.ofReal ((p - q) ^ 2) * ENNReal.ofReal (w x) := by
        rw [mul_comm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ x in Q, (2 * (ENNReal.ofReal ((u x - p) ^ 2) * ENNReal.ofReal (w x)) +
          2 * (ENNReal.ofReal ((u x - q) ^ 2) * ENNReal.ofReal (w x))) := by
        refine setLIntegral_mono' hQ fun x _ => ?_
        calc ENNReal.ofReal ((p - q) ^ 2) * ENNReal.ofReal (w x)
            ≤ (2 * ENNReal.ofReal ((u x - p) ^ 2) + 2 * ENNReal.ofReal ((u x - q) ^ 2)) *
                ENNReal.ofReal (w x) :=
              mul_le_mul_right' (gluing_ofReal_sq_sub_le_mid p (u x) q) _
          _ = _ := by ring
    _ = (∫⁻ x in Q, 2 * (ENNReal.ofReal ((u x - p) ^ 2) * ENNReal.ofReal (w x))) +
          ∫⁻ x in Q, 2 * (ENNReal.ofReal ((u x - q) ^ 2) * ENNReal.ofReal (w x)) :=
        lintegral_add_left' ((gluing_aemeasurable_sq_mul hQ hw hu p).const_mul 2) _
    _ = _ := by rw [lintegral_const_mul' _ _ h2, lintegral_const_mul' _ _ h2]

/-- A pointwise bound by a constant, integrated against a weight. -/
theorem gluing_lintegral_le_const_mul {Q : Set E} (hQ : MeasurableSet Q) {g : E → ℝ} {C : ℝ}
    (h : ∀ x ∈ Q, g x ≤ C) (v : E → ℝ) :
    ∫⁻ x in Q, ENNReal.ofReal (g x) * ENNReal.ofReal (v x) ≤
      ENNReal.ofReal C * ∫⁻ x in Q, ENNReal.ofReal (v x) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono' hQ fun x hx =>
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (h x hx)) _

/-! ## The steps of the proof on one cube -/

/-- Steps 1 to 3 of the paper's proof on one cube `Q`: for any constant `m`,
the integral of `(u - m)²` is controlled by the integrals of `(u - a i)²` over
the neighbours, by `(a j - m)²` and by the differences of the constants. -/
theorem gluing_step_two {ι : Type*} (Nbr : Finset ι) {M : ℕ} (hM : Nbr.card ≤ M)
    {Q : Set E} (hQ : MeasurableSet Q) {w u U : E → ℝ} (hw : Continuous w)
    (hu : ContinuousOn u Q) (a : ι → ℝ) (j : ι) (m : ℝ)
    (h1 : ∀ x ∈ Q, |u x - U x| ≤ ∑ i ∈ Nbr, |u x - a i|)
    (h2 : ∀ x ∈ Q, |U x - a j| ≤ ∑ i ∈ Nbr, |a i - a j|) :
    ∫⁻ x in Q, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) ≤
      2 * (M * ∑ i ∈ Nbr, ∫⁻ x in Q, ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x)) +
      (4 * ENNReal.ofReal ((a j - m) ^ 2) +
        4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2))) *
        ∫⁻ x in Q, ENNReal.ofReal (w x) := by
  have hWm : Measurable fun x : E => ENNReal.ofReal (w x) := hw.measurable.ennreal_ofReal
  have hpt : ∀ x ∈ Q, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) ≤
      2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x)) +
        (4 * ENNReal.ofReal ((a j - m) ^ 2) +
          4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2))) * ENNReal.ofReal (w x) := by
    intro x hx
    have e1 := gluing_ofReal_sq_sub_le (u x) (U x) m
    have e2 := gluing_ofReal_sq_sub_le (U x) (a j) m
    have e3 := gluing_ofReal_sq_le_card_sum Nbr hM (u x - U x) (fun i => u x - a i) (h1 x hx)
    have e4 := gluing_ofReal_sq_le_card_sum Nbr hM (U x - a j) (fun i => a i - a j) (h2 x hx)
    have e5 : ENNReal.ofReal ((u x - m) ^ 2) ≤
        2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2)) +
          (4 * ENNReal.ofReal ((a j - m) ^ 2) +
            4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2))) := by
      calc ENNReal.ofReal ((u x - m) ^ 2)
          ≤ 2 * ENNReal.ofReal ((u x - U x) ^ 2) + 2 * ENNReal.ofReal ((U x - m) ^ 2) := e1
        _ ≤ 2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2)) +
              2 * (2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)) +
                2 * ENNReal.ofReal ((a j - m) ^ 2)) :=
            add_le_add (mul_le_mul_left' e3 _)
              (mul_le_mul_left' (e2.trans (add_le_add (mul_le_mul_left' e4 _) le_rfl)) _)
        _ = _ := by ring
    calc ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)
        ≤ (2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2)) +
            (4 * ENNReal.ofReal ((a j - m) ^ 2) +
              4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)))) *
            ENNReal.ofReal (w x) := mul_le_mul_right' e5 _
      _ = _ := by rw [add_mul, mul_assoc, mul_assoc, Finset.sum_mul]
  have hsum : ∫⁻ x in Q, ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x) =
      ∑ i ∈ Nbr, ∫⁻ x in Q, ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x) :=
    lintegral_finset_sum' Nbr fun i _ => gluing_aemeasurable_sq_mul hQ hw hu (a i)
  calc ∫⁻ x in Q, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)
      ≤ ∫⁻ x in Q, (2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2) *
            ENNReal.ofReal (w x)) +
          (4 * ENNReal.ofReal ((a j - m) ^ 2) +
            4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2))) * ENNReal.ofReal (w x)) :=
        setLIntegral_mono' hQ hpt
    _ = (∫⁻ x in Q, 2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((u x - a i) ^ 2) *
            ENNReal.ofReal (w x))) +
          ∫⁻ x in Q, (4 * ENNReal.ofReal ((a j - m) ^ 2) +
            4 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2))) * ENNReal.ofReal (w x) :=
        lintegral_add_right _ (hWm.const_mul _)
    _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M), hsum, lintegral_const_mul _ hWm]

/-- Step 4 of the paper's proof on one cube, for the reference weight: the
mass times `(a j - m)²` is controlled by the integral of `(U - m)²` and by the
differences of the constants. -/
theorem gluing_step_four {ι : Type*} (Nbr : Finset ι) {M : ℕ} (hM : Nbr.card ≤ M)
    {Q : Set E} (hQ : MeasurableSet Q) {v U : E → ℝ} (hv : Continuous v) (a : ι → ℝ) (j : ι)
    (m : ℝ) (h2 : ∀ x ∈ Q, |U x - a j| ≤ ∑ i ∈ Nbr, |a i - a j|) :
    (∫⁻ x in Q, ENNReal.ofReal (v x)) * ENNReal.ofReal ((a j - m) ^ 2) ≤
      2 * (∫⁻ x in Q, ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x)) +
      2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)) *
        ∫⁻ x in Q, ENNReal.ofReal (v x) := by
  have hVm : Measurable fun x : E => ENNReal.ofReal (v x) := hv.measurable.ennreal_ofReal
  calc (∫⁻ x in Q, ENNReal.ofReal (v x)) * ENNReal.ofReal ((a j - m) ^ 2)
      = ∫⁻ x in Q, ENNReal.ofReal ((a j - m) ^ 2) * ENNReal.ofReal (v x) := by
        rw [mul_comm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ x in Q, (2 * (ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x)) +
          2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)) * ENNReal.ofReal (v x)) := by
        refine setLIntegral_mono' hQ fun x hx => ?_
        have e1 := gluing_ofReal_sq_sub_le_mid (a j) (U x) m
        have e4 := gluing_ofReal_sq_le_card_sum Nbr hM (U x - a j) (fun i => a i - a j)
          (h2 x hx)
        calc ENNReal.ofReal ((a j - m) ^ 2) * ENNReal.ofReal (v x)
            ≤ (2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)) +
                2 * ENNReal.ofReal ((U x - m) ^ 2)) * ENNReal.ofReal (v x) :=
              mul_le_mul_right' (e1.trans (add_le_add (mul_le_mul_left' e4 _) le_rfl)) _
          _ = _ := by ring
    _ = (∫⁻ x in Q, 2 * (ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x))) +
          ∫⁻ x in Q, 2 * (M * ∑ i ∈ Nbr, ENNReal.ofReal ((a i - a j) ^ 2)) *
            ENNReal.ofReal (v x) := lintegral_add_right _ (hVm.const_mul _)
    _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤), lintegral_const_mul _ hVm]

/-! ## Geometry of the covering -/

/-- A cube of diameter at most `ρ` that meets the ball of radius `ρ` lies in
the ball of radius `2 ρ`. -/
theorem gluing_cube_subset_ball_of_meets {c x0 : E} {s ρ : ℝ} (hd : Real.sqrt n * s ≤ ρ)
    (hmeet : (cube c s ∩ ball x0 ρ).Nonempty) : cube c s ⊆ ball x0 (2 * ρ) := by
  obtain ⟨z, hz, hzb⟩ := hmeet
  intro y hy
  have h1 := cube_subset_closedBall c s hz
  have h2 := cube_subset_closedBall c s hy
  rw [mem_closedBall] at h1 h2
  rw [mem_ball] at hzb ⊢
  have h3 := dist_triangle4 y c z x0
  rw [dist_comm c z] at h3
  linarith

/-- In positive dimension the side of a cube is at most its diameter. -/
theorem gluing_side_le_of_diam_le (hn : 0 < n) {s ρ : ℝ} (hs : 0 ≤ s)
    (hd : Real.sqrt n * s ≤ ρ) : s ≤ ρ := by
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  nlinarith

/-- If a ball of positive radius lies in a ball, so do the closed balls. -/
theorem gluing_closedBall_subset_of_ball_subset {a x0 : E} {r r' : ℝ} (hr : 0 < r)
    (h : ball a r ⊆ ball x0 r') : closedBall a r ⊆ closedBall x0 r' := by
  rw [← closure_ball a hr.ne']
  exact (closure_mono h).trans closure_ball_subset_closedBall

/-! ## The gluing argument for one family of cubes -/

/-- The gluing argument for one finite family of cubes, with the glued
function `U` and the cell constants `a j` given. The hypotheses on `U` are the
properties of `∑ j, a j * ψ j` for the partition of unity of `CubePartition`.
The hypotheses `H2` and `H5` are the two estimates that the paper obtains
from the Poincare inequality on the balls `B_j` (steps 2 and 5). -/
theorem gluing_core_family {ι : Type*} [Fintype ι] {κ : ℝ} (hκ : 1 < κ)
    (c : ι → E) (s : ι → ℝ) (b : ι → E) (R : ι → ℝ) {w v : E → ℝ} (x0 : E) (ρ : ℝ)
    {N0 Nb M : ℕ} {K2 : ℝ} {G A Pν : ℝ≥0∞} (hG : G ≠ ⊤) (hK2 : 0 ≤ K2)
    (hw : Continuous w) (hv : Continuous v) (hs : ∀ j, 0 < s j)
    (hcov : closedBall x0 (2 * ρ) ⊆ ⋃ j, cube (c j) (s j))
    (hN0 : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0)
    (hdiam : ∀ j, Real.sqrt n * s j ≤ ρ) (hsρ : ∀ j, s j ≤ ρ)
    (hM : ∀ j, (cubeNeighbors κ c s j).card ≤ M)
    (hball : ∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j))
    (hin : ∀ j, ball (b j) (R j) ⊆ ball x0 (4 * ρ))
    (hNb : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ ball (b i) (R i)) → T.card ≤ Nb)
    (hG1 : ∀ j, ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x) ≤
      G * ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (v x))
    (hG2 : ∀ j, ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (v x) ≤
      G * ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x))
    (hν : poincareAt volume v Pν 1 x0 (2 * ρ))
    {u U : E → ℝ} (a : ι → ℝ) (hu : ContinuousOn u (closedBall x0 (4 * ρ)))
    (hU1 : ContDiffOn ℝ 1 U (closedBall x0 (2 * ρ)))
    (hUu : ∀ j, ∀ x ∈ cube (c j) (s j),
      |u x - U x| ≤ ∑ i ∈ cubeNeighbors κ c s j, |u x - a i|)
    (hUa : ∀ j, ∀ x ∈ cube (c j) (s j),
      |U x - a j| ≤ ∑ i ∈ cubeNeighbors κ c s j, |a i - a j|)
    (hUg : ∀ j, ∀ x ∈ cube (c j) (s j),
      ‖fderiv ℝ U x‖ ^ 2 ≤ K2 / s j ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2)
    (H2 : ∀ i j, cubeNeighbor κ c s i j →
      ∫⁻ x in cube (c j) (s j), ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x) ≤
        A * ENNReal.ofReal (s j ^ 2) *
          ∫⁻ x in ball (b i) (R i), ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x))
    (H5 : ∀ i j, cubeNeighbor κ c s i j →
      (∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x)) * ENNReal.ofReal ((a i - a j) ^ 2) ≤
        A * ENNReal.ofReal (s j ^ 2) *
          ((∫⁻ x in ball (b i) (R i),
              ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x)) +
            ∫⁻ x in ball (b j) (R j),
              ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x))) :
    weightedVariance (volume.restrict (ball x0 ρ)) (fun x => ENNReal.ofReal (w x)) u ≤
      A * (2 * M * Nb) * (6 * M + 8 * M * G ^ 2 + 32 * G ^ 2 * N0 * Pν * ENNReal.ofReal K2) *
        ENNReal.ofReal (ρ ^ 2) *
        weightedEnergy (volume.restrict (ball x0 (4 * ρ))) (fun x => ENNReal.ofReal (w x)) u := by
  classical
  have hκ0 : 0 ≤ κ := by linarith
  have hself : ∀ j, j ∈ cubeNeighbors κ c s j := fun j =>
    cubeNeighbors_mem_iff.mpr (cubeNeighbor_refl hκ0 (hs j).le)
  have hsym : ∀ i j, i ∈ cubeNeighbors κ c s j → j ∈ cubeNeighbors κ c s i := fun i j h =>
    cubeNeighbors_mem_iff.mpr (cubeNeighbor_symm (cubeNeighbors_mem_iff.mp h))
  have hQB : ∀ j, cube (c j) (s j) ⊆ ball (b j) (R j) := fun j =>
    (cube_subset_enlarged (c j) hκ.le (hs j).le).trans
      (hball j j (cubeNeighbor_refl hκ0 (hs j).le))
  have hQ4 : ∀ j, cube (c j) (s j) ⊆ closedBall x0 (4 * ρ) := fun j =>
    ((hQB j).trans (hin j)).trans ball_subset_closedBall
  have hQm : ∀ j, MeasurableSet (cube (c j) (s j)) := fun j => cube_measurableSet _ _
  have hB2 : ball x0 ρ ⊆ closedBall x0 (2 * ρ) := by
    intro x hx
    rw [mem_ball] at hx
    rw [mem_closedBall]
    linarith [dist_nonneg (x := x) (y := x0)]
  have hJ1sub : ∀ j ∈ Finset.univ.filter
      (fun j => (cube (c j) (s j) ∩ ball x0 ρ).Nonempty),
      cube (c j) (s j) ⊆ ball x0 (2 * ρ) := fun j hj =>
    gluing_cube_subset_ball_of_meets (hdiam j) (Finset.mem_filter.mp hj).2
  have hEb : ∑ j, ∫⁻ x in ball (b j) (R j),
      ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x) ≤
      Nb * ∫⁻ x in ball x0 (4 * ρ),
        ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x) :=
    gluing_sum_lintegral_le_of_overlap volume Finset.univ (fun j => ball (b j) (R j))
      (fun _ _ => measurableSet_ball) measurableSet_ball (fun j _ => hin j) Nb hNb _
  obtain ⟨hT1, hT2, hT3⟩ := gluing_assembly_pairs (cubeNeighbors κ c s) hsym hM
    (fun j => ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x))
    (fun j => ∫⁻ x in ball (b j) (R j),
      ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x))
    (fun j => ENNReal.ofReal (s j ^ 2)) (fun j => ENNReal.ofReal (K2 / s j ^ 2))
    (fun i j => ∫⁻ x in cube (c j) (s j),
      ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x))
    (fun i j => ENNReal.ofReal ((a i - a j) ^ 2))
    (r2 := ENNReal.ofReal (ρ ^ 2)) (k2 := ENNReal.ofReal K2) (A := A)
    (fun j => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hs j).le (hsρ j) 2))
    (fun j => by
      rw [← ENNReal.ofReal_mul (div_nonneg hK2 (sq_nonneg _))]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      have := (hs j).ne'
      field_simp)
    (fun j i hi => H2 i j (cubeNeighbors_mem_iff.mp hi))
    (fun j i hi => H5 i j (cubeNeighbors_mem_iff.mp hi))
    hEb
  have h8 : ⨅ m : ℝ, ∫⁻ x in ball x0 (2 * ρ),
      ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x) ≤
      Pν * (4 * ENNReal.ofReal (ρ ^ 2)) *
        ∫⁻ x in ball x0 (2 * ρ), ENNReal.ofReal (‖fderiv ℝ U x‖ ^ 2) * ENNReal.ofReal (v x) := by
    have h := hν U (by rwa [one_mul])
    rw [one_mul] at h
    have e : ENNReal.ofReal ((2 * ρ) ^ 2) = 4 * ENNReal.ofReal (ρ ^ 2) := by
      rw [mul_pow, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [e] at h
    exact h
  have h9 : ∫⁻ x in ball x0 (2 * ρ),
      ENNReal.ofReal (‖fderiv ℝ U x‖ ^ 2) * ENNReal.ofReal (v x) ≤
      ∑ j, ENNReal.ofReal (K2 / s j ^ 2) *
        ((∑ i ∈ cubeNeighbors κ c s j, ENNReal.ofReal ((a i - a j) ^ 2)) *
          ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (v x)) := by
    refine (gluing_lintegral_le_sum_cover volume (fun j => cube (c j) (s j))
      (ball_subset_closedBall.trans hcov) _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (gluing_lintegral_le_const_mul (hQm j) (hUg j) v).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (div_nonneg hK2 (sq_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _, mul_assoc]
  have key := gluing_assembly (cubeNeighbors κ c s) (M := M)
    (Finset.univ.filter (fun j => (cube (c j) (s j) ∩ ball x0 ρ).Nonempty))
    (fun j => ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x))
    (fun j => ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (v x))
    (fun j => ENNReal.ofReal (K2 / s j ^ 2))
    (fun i j => ∫⁻ x in cube (c j) (s j),
      ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x))
    (fun i j => ENNReal.ofReal ((a i - a j) ^ 2))
    (r2 := ENNReal.ofReal (ρ ^ 2)) (Pν := Pν) (N0 := N0)
    hG hT1 hT2 hT3 hG1 hG2
    (fun m => ∫⁻ x in ball x0 ρ, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x))
    (fun m => ∫⁻ x in ball x0 (2 * ρ), ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x))
    (fun j m => ENNReal.ofReal ((a j - m) ^ 2))
    (fun j m => ∫⁻ x in cube (c j) (s j),
      ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x))
    (fun j m => ∫⁻ x in cube (c j) (s j),
      ENNReal.ofReal ((U x - m) ^ 2) * ENNReal.ofReal (v x))
    (fun m => gluing_lintegral_le_sum_meeting volume (fun j => cube (c j) (s j))
      (hB2.trans hcov) _ _ (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
    (fun m j _ => gluing_step_two (cubeNeighbors κ c s j) (hM j) (hQm j) hw
      (hu.mono (hQ4 j)) a j m (hUu j) (hUa j))
    (fun m j => gluing_step_four (cubeNeighbors κ c s j) (hM j) (hQm j) hv a j m (hUa j))
    (fun m => gluing_sum_lintegral_le_of_overlap volume _ (fun j => cube (c j) (s j))
      (fun j _ => hQm j) measurableSet_ball hJ1sub N0 hN0 _)
    h8 h9
  unfold weightedVariance weightedEnergy
  refine key.trans (le_of_eq ?_)
  ring

end Cube

/-- Dimension zero: the space is a point and every variance vanishes. -/
theorem gluing_variance_dim_zero (μ : Measure (EuclideanSpace ℝ (Fin 0)))
    (W : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞) (u : EuclideanSpace ℝ (Fin 0) → ℝ) :
    weightedVariance μ W u = 0 := by
  have hx : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x => by
    ext i
    exact i.elim0
  unfold weightedVariance
  refine le_antisymm (iInf_le_of_le (u 0) ?_) (zero_le _)
  have h0 : ∀ x, ENNReal.ofReal ((u x - u 0) ^ 2) * W x = 0 := fun x => by
    rw [hx x]
    simp
  simp [h0]

/-! ## The gluing lemma with the cell constants left open -/

/-- **The gluing argument, steps 1, 3, 4 and 6 of the paper's proof.** The
constant `K` is chosen before the family of cubes, the ball and the weights.
The cell constants `a j` are arbitrary real numbers subject to the two
estimates that the paper derives from (G2): the step-2 estimate (`u - a i`
on a neighbouring cube `j`) and the step-5 estimate (`a i - a j` for
neighbours). The two theorems after this one supply them. -/
theorem gluing_core (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 Nb : ℕ) (Λ : ℝ) {G A Pν : ℝ≥0∞}
    (hG : G ≠ ⊤) (hA : A ≠ ⊤) (hPν : Pν ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin n)) (R : ι → ℝ)
        (w v : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
        Continuous w → Continuous v → (∀ j, 0 < s j) →
        closedBall x0 (2 * ρ) ⊆ ⋃ j, cube (c j) (s j) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ j, Real.sqrt n * s j ≤ ρ) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j)) →
        (∀ j, ball (b j) (R j) ⊆ ball x0 (4 * ρ)) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ ball (b i) (R i)) → T.card ≤ Nb) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j))) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j))) →
        poincareAt volume v Pν 1 x0 (2 * ρ) →
        ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (a : ι → ℝ),
          ContDiffOn ℝ 1 u (closedBall x0 (4 * ρ)) →
          (∀ i j, cubeNeighbor κ c s i j →
            ∫⁻ x in cube (c j) (s j), ENNReal.ofReal ((u x - a i) ^ 2) * ENNReal.ofReal (w x) ≤
              A * ENNReal.ofReal (s j ^ 2) *
                ∫⁻ x in ball (b i) (R i),
                  ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x)) →
          (∀ i j, cubeNeighbor κ c s i j →
            (∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x)) *
                ENNReal.ofReal ((a i - a j) ^ 2) ≤
              A * ENNReal.ofReal (s j ^ 2) *
                ((∫⁻ x in ball (b i) (R i),
                    ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x)) +
                  ∫⁻ x in ball (b j) (R j),
                    ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x))) →
          weightedVariance (volume.restrict (ball x0 ρ)) (fun x => ENNReal.ofReal (w x)) u ≤
            (K * ENNReal.ofReal (ρ ^ 2)) *
              weightedEnergy (volume.restrict (ball x0 (4 * ρ)))
                (fun x => ENNReal.ofReal (w x)) u := by
  obtain ⟨K1, K2, hK1, hK2, hpart⟩ := cube_exists_partition_of_unity.{u} n hκ N0 Λ
  obtain ⟨M, hMcard⟩ := cubeNeighbors_exists_card_bound.{u} n hκ N0 Λ
  refine ⟨A * (2 * M * Nb) *
    (6 * M + 8 * M * G ^ 2 + 32 * G ^ 2 * N0 * Pν * ENNReal.ofReal K2), ?_, ?_⟩
  · finiteness
  intro ι _ c s b R w v x0 ρ hw hv hs hcov hN0 hdiam hΛ hball hin hNb hG1 hG2 hν u a hu H2 H5
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [gluing_variance_dim_zero]
    exact zero_le _
  obtain ⟨ψ, V, -, -, -, hψ01, -, -, -, hUc1, hUw, hUa, hgrad⟩ := hpart ι c s hs
  obtain ⟨-, hUg⟩ := hgrad hN0 hΛ
  have hQm : ∀ j, MeasurableSet (cube (c j) (s j)) := fun j => cube_measurableSet _ _
  refine gluing_core_family hκ c s b R x0 ρ hG hK2 hw hv hs hcov hN0 hdiam
    (fun j => gluing_side_le_of_diam_le hn (hs j).le (hdiam j)) (hMcard ι c s hs hN0 hΛ)
    hball hin hNb ?_ ?_ hν a hu.continuousOn (hUc1 a _ hcov)
    (fun j x hx => (hUw a (u x) j x hx).trans (Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_left (abs_nonneg _) (hψ01 i x).2))
    (fun j x hx => hUa a j x hx) (fun j x hx => hUg a j x hx) H2 H5
  · intro j
    have h := hG1 j
    rwa [withDensity_apply _ (hQm j), withDensity_apply _ (hQm j)] at h
  · intro j
    have h := hG2 j
    rwa [withDensity_apply _ (hQm j), withDensity_apply _ (hQm j)] at h

/-! ## The two estimates from the Poincare inequality on the balls -/

/-- Radii against sides: `R ≤ Cr * s i` and `s i ≤ Λ * s j` give
`R² ≤ (Cr Λ)² s j²`. -/
theorem gluing_radius_sq_le {R si sj Cr Λ : ℝ} (hR0 : 0 ≤ R) (hsi : 0 < si)
    (hR : R ≤ Cr * si) (hΛ : si ≤ Λ * sj) :
    ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal ((Cr * Λ) ^ 2) * ENNReal.ofReal (sj ^ 2) := by
  have hCr : 0 ≤ Cr := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h hsi
    linarith
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : R ≤ Cr * Λ * sj := by
    have := mul_le_mul_of_nonneg_left hΛ hCr
    linarith
  calc R ^ 2 ≤ (Cr * Λ * sj) ^ 2 := pow_le_pow_left₀ hR0 h1 2
    _ = (Cr * Λ) ^ 2 * sj ^ 2 := by ring

section Means

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Step 2 of the paper's proof, with the mean on a neighbouring cube `Q'`:
`a'` is a constant with the mean property on `Q'`, `m` any constant, `B` a set
containing both cubes. The mass comparison `hmass` is where the paper needs
local doubling. -/
theorem gluing_mean_step_two {Q Q' B : Set E} (hQ : MeasurableSet Q) {w u : E → ℝ}
    (hw : Continuous w) {Kb : ℝ≥0∞} (a' m : ℝ)
    (hmean : (∫⁻ x in Q', ENNReal.ofReal (w x)) * ENNReal.ofReal ((a' - m) ^ 2) ≤
      ∫⁻ x in Q', ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x))
    (hQ'B : Q' ⊆ B) (hQB : Q ⊆ B)
    (hmass : ∫⁻ x in Q, ENNReal.ofReal (w x) ≤ Kb * ∫⁻ x in Q', ENNReal.ofReal (w x)) :
    ∫⁻ x in Q, ENNReal.ofReal ((u x - a') ^ 2) * ENNReal.ofReal (w x) ≤
      (2 + 2 * Kb) * ∫⁻ x in B, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) := by
  have hWm : Measurable fun x : E => ENNReal.ofReal (w x) := hw.measurable.ennreal_ofReal
  calc ∫⁻ x in Q, ENNReal.ofReal ((u x - a') ^ 2) * ENNReal.ofReal (w x)
      ≤ ∫⁻ x in Q, (2 * (ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)) +
          2 * ENNReal.ofReal ((a' - m) ^ 2) * ENNReal.ofReal (w x)) := by
        refine setLIntegral_mono' hQ fun x _ => ?_
        have e := gluing_ofReal_le_two_add (p := (u x - a') ^ 2) (q := (u x - m) ^ 2)
          (r := (a' - m) ^ 2) (sq_nonneg _) (sq_nonneg _)
          (by nlinarith [sq_nonneg (u x - m + (a' - m))])
        calc ENNReal.ofReal ((u x - a') ^ 2) * ENNReal.ofReal (w x)
            ≤ (2 * ENNReal.ofReal ((u x - m) ^ 2) + 2 * ENNReal.ofReal ((a' - m) ^ 2)) *
                ENNReal.ofReal (w x) := mul_le_mul_right' e _
          _ = _ := by ring
    _ = (∫⁻ x in Q, 2 * (ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x))) +
          ∫⁻ x in Q, 2 * ENNReal.ofReal ((a' - m) ^ 2) * ENNReal.ofReal (w x) :=
        lintegral_add_right _ (hWm.const_mul _)
    _ = 2 * (∫⁻ x in Q, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)) +
          2 * ENNReal.ofReal ((a' - m) ^ 2) * ∫⁻ x in Q, ENNReal.ofReal (w x) := by
        rw [lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤), lintegral_const_mul _ hWm]
    _ ≤ 2 * (∫⁻ x in B, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)) +
          2 * ENNReal.ofReal ((a' - m) ^ 2) * (Kb * ∫⁻ x in Q', ENNReal.ofReal (w x)) :=
        add_le_add (mul_le_mul_left' (lintegral_mono_set hQB) 2) (mul_le_mul_left' hmass _)
    _ = 2 * (∫⁻ x in B, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)) +
          2 * Kb * ((∫⁻ x in Q', ENNReal.ofReal (w x)) * ENNReal.ofReal ((a' - m) ^ 2)) := by
        ring
    _ ≤ 2 * (∫⁻ x in B, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x)) +
          2 * Kb * ∫⁻ x in B, ENNReal.ofReal ((u x - m) ^ 2) * ENNReal.ofReal (w x) :=
        add_le_add le_rfl (mul_le_mul_left' (hmean.trans (lintegral_mono_set hQ'B)) _)
    _ = _ := by ring

/-- Step 5 of the paper's proof with numbers: two cell means compared through
a common constant `m`. `VB` is the integral of `(u - m)²` over a ball
containing both cubes; `hmi`, `hmj` are the mean properties on the two cubes
followed by the inclusion in the ball; `hmass` is the mass comparison. -/
theorem gluing_mean_step_five {muQi muQj VB Kb : ℝ≥0∞} (ai aj m : ℝ)
    (hmi : muQi * ENNReal.ofReal ((ai - m) ^ 2) ≤ VB)
    (hmj : muQj * ENNReal.ofReal ((aj - m) ^ 2) ≤ VB) (hmass : muQj ≤ Kb * muQi) :
    muQj * ENNReal.ofReal ((ai - aj) ^ 2) ≤ (2 + 2 * Kb) * VB := by
  have e := gluing_ofReal_le_two_add (p := (ai - aj) ^ 2) (q := (ai - m) ^ 2)
    (r := (aj - m) ^ 2) (sq_nonneg _) (sq_nonneg _)
    (by nlinarith [sq_nonneg (ai - m + (aj - m))])
  calc muQj * ENNReal.ofReal ((ai - aj) ^ 2)
      ≤ muQj * (2 * ENNReal.ofReal ((ai - m) ^ 2) + 2 * ENNReal.ofReal ((aj - m) ^ 2)) :=
        mul_le_mul_left' e _
    _ = 2 * (muQj * ENNReal.ofReal ((ai - m) ^ 2)) +
          2 * (muQj * ENNReal.ofReal ((aj - m) ^ 2)) := by ring
    _ ≤ 2 * (Kb * muQi * ENNReal.ofReal ((ai - m) ^ 2)) + 2 * VB :=
        add_le_add (mul_le_mul_left' (mul_le_mul_right' hmass _) 2) (mul_le_mul_left' hmj 2)
    _ = 2 * Kb * (muQi * ENNReal.ofReal ((ai - m) ^ 2)) + 2 * VB := by ring
    _ ≤ 2 * Kb * VB + 2 * VB := add_le_add (mul_le_mul_left' hmi _) le_rfl
    _ = _ := by ring

/-- Iterated doubling at one centre, using doubling only at the radii
`2 ^ l * r`, `l < k`. -/
theorem gluing_doubling_iterate {w : E → ℝ} {D : ℝ≥0∞} (a : E) (r : ℝ) (k : ℕ)
    (h : ∀ l < k, doublingAt volume w D a (2 ^ l * r)) :
    (volume.withDensity fun x => ENNReal.ofReal (w x)) (ball a (2 ^ k * r)) ≤
      D ^ k * (volume.withDensity fun x => ENNReal.ofReal (w x)) (ball a r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : (2 : ℝ) ^ (k + 1) * r = 2 * (2 ^ k * r) := by ring
    rw [h2, pow_succ, mul_comm (D ^ k) D, mul_assoc]
    exact (h k (Nat.lt_succ_self k)).trans
      (mul_le_mul_left' (ih fun l hl => h l (Nat.lt_succ_of_lt hl)) D)

end Means

/-! ## (G2b) from local doubling -/

/-- **Local doubling gives (G2b).** If the weight is doubling at balls centred
in `B_j` with radius at most the radius of `B_j`, then
`μ (B_j) ≤ D ^ k * μ (Q_i)` for every neighbour `i` of `j` (in particular for
`i = j`). The number of doubling steps `k` depends only on `Cr` and `Λ`. The
family need not be finite. -/
theorem gluing_ball_le_cube_of_doubling (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (Λ Cr : ℝ) :
    ∃ k : ℕ,
      ∀ (ι : Type u) (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin n)) (R : ι → ℝ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
        (D : ℝ≥0∞),
        (∀ j, 0 < s j) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j)) →
        (∀ j, R j ≤ Cr * s j) →
        (∀ j, ∀ a ∈ ball (b j) (R j), ∀ r, 0 < r → r ≤ R j → doublingAt volume w D a r) →
        ∀ i j, cubeNeighbor κ c s i j →
          (volume.withDensity fun x => ENNReal.ofReal (w x)) (ball (b j) (R j)) ≤
            D ^ k * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c i) (s i)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * Cr * Λ) (one_lt_two (α := ℝ))
  refine ⟨k, ?_⟩
  intro ι c s b R w D hs hΛ hball hRs hdoub i j hij
  have hκ0 : 0 ≤ κ := by linarith
  have hci : c i ∈ ball (b j) (R j) :=
    hball i j hij (cube_center_mem (c i) (mul_nonneg hκ0 (hs i).le))
  have hR0 : 0 < R j := pos_of_mem_ball hci
  have hCr : 0 ≤ Cr := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (hs j)
    linarith [hRs j]
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have h2k : (2 : ℝ) ^ k * (2 * R j / 2 ^ k) = 2 * R j := by
    field_simp
  have hsub1 : ball (b j) (R j) ⊆ ball (c i) (2 ^ k * (2 * R j / 2 ^ k)) := by
    rw [h2k]
    intro x hx
    rw [mem_ball] at hx hci ⊢
    have h3 := dist_triangle x (b j) (c i)
    rw [dist_comm (b j) (c i)] at h3
    linarith
  have hsub2 : ball (c i) (2 * R j / 2 ^ k) ⊆ cube (c i) (s i) := by
    refine (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)).trans
      (cube_closedBall_subset (c i) (s i))
    rw [div_le_iff₀ hpk]
    have h1 : R j ≤ Cr * (Λ * s i) :=
      (hRs j).trans (mul_le_mul_of_nonneg_left (hΛ j i (cubeNeighbor_symm hij)) hCr)
    have h3 : 4 * Cr * Λ * s i ≤ 2 ^ k * s i := mul_le_mul_of_nonneg_right hk.le (hs i).le
    nlinarith
  have hiter := gluing_doubling_iterate (w := w) (D := D) (c i) (2 * R j / 2 ^ k) k
    (fun l hl => hdoub j (c i) hci (2 ^ l * (2 * R j / 2 ^ k)) (by positivity) (by
      have hpow : (2 : ℝ) ^ l * 2 ≤ 2 ^ k := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ one_le_two hl
      rw [← mul_div_assoc, div_le_iff₀ hpk]
      calc (2 : ℝ) ^ l * (2 * R j) = (2 ^ l * 2) * R j := by ring
        _ ≤ 2 ^ k * R j := mul_le_mul_of_nonneg_right hpow hR0.le
        _ = R j * 2 ^ k := mul_comm _ _))
  calc (volume.withDensity fun x => ENNReal.ofReal (w x)) (ball (b j) (R j))
      ≤ (volume.withDensity fun x => ENNReal.ofReal (w x))
          (ball (c i) (2 ^ k * (2 * R j / 2 ^ k))) := measure_mono hsub1
    _ ≤ D ^ k * (volume.withDensity fun x => ENNReal.ofReal (w x))
          (ball (c i) (2 * R j / 2 ^ k)) := hiter
    _ ≤ D ^ k * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c i) (s i)) :=
        mul_le_mul_left' (measure_mono hsub2) _

/-! ## The gluing lemma -/

/-- **The gluing lemma (`lem:glue`), by the paper's proof.** The cell
constants are the `μ`-means of `u` on the cubes, as in the paper. (G2) enters
as the Poincare inequality on each `B_j` and as (G2b), the mass comparison
`μ (B_j) ≤ Kb * μ (Q_j)`, which is what the paper draws from local doubling
(`gluing_ball_le_cube_of_doubling`). The constant `K` is finite and is chosen
before the family of cubes, the ball and the weights. -/
theorem gluing_lemma (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 Nb : ℕ) (Λ Cr : ℝ)
    {G P Kb Pν : ℝ≥0∞} (hG : G ≠ ⊤) (hP : P ≠ ⊤) (hKb : Kb ≠ ⊤) (hPν : Pν ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin n)) (R : ι → ℝ)
        (w v : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
        Continuous w → (∀ x, 0 ≤ w x) → Continuous v → (∀ j, 0 < s j) →
        closedBall x0 (2 * ρ) ⊆ ⋃ j, cube (c j) (s j) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ j, Real.sqrt n * s j ≤ ρ) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j)) →
        (∀ j, R j ≤ Cr * s j) →
        (∀ j, ball (b j) (R j) ⊆ ball x0 (4 * ρ)) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ ball (b i) (R i)) → T.card ≤ Nb) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j))) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j))) →
        (∀ j, poincareAt volume w P 1 (b j) (R j)) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (w x)) (ball (b j) (R j)) ≤
          Kb * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j))) →
        poincareAt volume v Pν 1 x0 (2 * ρ) →
        poincareAt volume w K 4 x0 ρ := by
  obtain ⟨K, hK, hcore⟩ := gluing_core.{u} n hκ N0 Nb Λ hG
    (A := (2 + 2 * Kb) * (P * ENNReal.ofReal ((Cr * Λ) ^ 2))) (by finiteness) hPν
  refine ⟨K, hK, ?_⟩
  intro ι _ c s b R w v x0 ρ hw hw0 hv hs hcov hN0 hdiam hΛ hball hRs hin hNb hG1 hG2 hPj
    hG2b hν u hu
  have hκ0 : 0 ≤ κ := by linarith
  have hrefl : ∀ j, cubeNeighbor κ c s j j := fun j => cubeNeighbor_refl hκ0 (hs j).le
  have hR0 : ∀ j, 0 < R j := fun j =>
    pos_of_mem_ball (hball j j (hrefl j) (cube_center_mem (c j) (mul_nonneg hκ0 (hs j).le)))
  have huj : ∀ j, ContDiffOn ℝ 1 u (closedBall (b j) (R j)) := fun j =>
    hu.mono (gluing_closedBall_subset_of_ball_subset (hR0 j) (hin j))
  choose m hm using fun j => gluing_ball_minimizer hw hw0 (hPj j) (huj j)
  have hQB : ∀ i j, cubeNeighbor κ c s i j → cube (c j) (s j) ⊆ ball (b i) (R i) :=
    fun i j h => (cube_subset_enlarged (c j) hκ.le (hs j).le).trans
      (hball j i (cubeNeighbor_symm h))
  have hQ4 : ∀ j, cube (c j) (s j) ⊆ closedBall x0 (4 * ρ) := fun j =>
    ((hQB j j (hrefl j)).trans (hin j)).trans ball_subset_closedBall
  have hQm : ∀ j, MeasurableSet (cube (c j) (s j)) := fun j => cube_measurableSet _ _
  have hmean : ∀ j (t : ℝ), (∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x)) *
      ENNReal.ofReal ((⨍ y, u y ∂(volume.restrict (cube (c j) (s j))).withDensity
        (fun x => ENNReal.ofReal (w x)) - t) ^ 2) ≤
      ∫⁻ x in cube (c j) (s j), ENNReal.ofReal ((u x - t) ^ 2) * ENNReal.ofReal (w x) :=
    fun j t => gluing_compact_mean_sq_le hw hw0 (gluing_cube_isCompact _ _)
      (hu.continuousOn.mono (hQ4 j)) t
  have hmass : ∀ i j, cubeNeighbor κ c s i j →
      ∫⁻ x in cube (c j) (s j), ENNReal.ofReal (w x) ≤
        Kb * ∫⁻ x in cube (c i) (s i), ENNReal.ofReal (w x) := by
    intro i j hij
    rw [← withDensity_apply _ (hQm j), ← withDensity_apply _ (hQm i)]
    exact (measure_mono (hQB i j hij)).trans (hG2b i)
  refine hcore ι c s b R w v x0 ρ hw hv hs hcov hN0 hdiam hΛ hball hin hNb hG1 hG2 hν u
    (fun j => ⨍ y, u y ∂(volume.restrict (cube (c j) (s j))).withDensity
      (fun x => ENNReal.ofReal (w x))) hu ?_ ?_
  · intro i j hij
    have h1 := gluing_mean_step_two (hQm j) hw _ (m i) (hmean i (m i)) (hQB i i (hrefl i))
      (hQB i j hij) (hmass i j hij)
    refine h1.trans ?_
    refine (mul_le_mul_left' (hm i) _).trans ?_
    refine (mul_le_mul_left' (mul_le_mul_right' (mul_le_mul_left'
      (gluing_radius_sq_le (hR0 i).le (hs i) (hRs i) (hΛ i j hij)) P) _) _).trans
      (le_of_eq ?_)
    ring
  · intro i j hij
    have h1 := gluing_mean_step_five (Kb := Kb) _ _ (m j)
      ((hmean i (m j)).trans (lintegral_mono_set (hQB j i (cubeNeighbor_symm hij))))
      ((hmean j (m j)).trans (lintegral_mono_set (hQB j j (hrefl j)))) (hmass i j hij)
    refine h1.trans ?_
    refine (mul_le_mul_left' (hm j) _).trans ?_
    refine (mul_le_mul_left' (mul_le_mul_right' (mul_le_mul_left'
      (gluing_radius_sq_le (hR0 j).le (hs j) (hRs j) (hΛ j j (hrefl j))) P) _) _).trans ?_
    calc (2 + 2 * Kb) * (P * (ENNReal.ofReal ((Cr * Λ) ^ 2) * ENNReal.ofReal (s j ^ 2)) *
          ∫⁻ x in ball (b j) (R j), ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x))
        = (2 + 2 * Kb) * (P * ENNReal.ofReal ((Cr * Λ) ^ 2)) * ENNReal.ofReal (s j ^ 2) *
          ∫⁻ x in ball (b j) (R j),
            ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x) := by ring
      _ ≤ _ := mul_le_mul_left' le_add_self _

/-- **The gluing lemma as stated in the paper**, with (G2) in the paper's
form: the Poincare inequality on each `B_j` and doubling at balls centred in
`B_j` with radius at most the radius of `B_j`. -/
theorem gluing_lemma_of_local_doubling (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 Nb : ℕ) (Λ Cr : ℝ)
    {G P D Pν : ℝ≥0∞} (hG : G ≠ ⊤) (hP : P ≠ ⊤) (hD : D ≠ ⊤) (hPν : Pν ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin n)) (R : ι → ℝ)
        (w v : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
        Continuous w → (∀ x, 0 ≤ w x) → Continuous v → (∀ j, 0 < s j) →
        closedBall x0 (2 * ρ) ⊆ ⋃ j, cube (c j) (s j) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ j, Real.sqrt n * s j ≤ ρ) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j)) →
        (∀ j, R j ≤ Cr * s j) →
        (∀ j, ball (b j) (R j) ⊆ ball x0 (4 * ρ)) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ ball (b i) (R i)) → T.card ≤ Nb) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j))) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j))) →
        (∀ j, poincareAt volume w P 1 (b j) (R j)) →
        (∀ j, ∀ a ∈ ball (b j) (R j), ∀ r, 0 < r → r ≤ R j → doublingAt volume w D a r) →
        poincareAt volume v Pν 1 x0 (2 * ρ) →
        poincareAt volume w K 4 x0 ρ := by
  obtain ⟨k, hk⟩ := gluing_ball_le_cube_of_doubling.{u} n hκ Λ Cr
  obtain ⟨K, hK, h⟩ := gluing_lemma.{u} n hκ N0 Nb Λ Cr hG hP (Kb := D ^ k)
    (ENNReal.pow_ne_top hD) hPν
  refine ⟨K, hK, ?_⟩
  intro ι _ c s b R w v x0 ρ hw hw0 hv hs hcov hN0 hdiam hΛ hball hRs hin hNb hG1 hG2 hPj
    hdoub hν
  exact h ι c s b R w v x0 ρ hw hw0 hv hs hcov hN0 hdiam hΛ hball hRs hin hNb hG1 hG2 hPj
    (fun j => hk ι c s b R w D hs hΛ hball hRs hdoub j j
      (cubeNeighbor_refl (by linarith) (hs j).le)) hν

/-- **The gluing lemma without doubling.** If the cell constants are taken to
be the `μ`-means of `u` on the balls `B_j` instead of on the cubes `Q_j`, the
doubling half of (G2) is not needed: the Poincare inequality on each `B_j`
suffices. This is not the paper's proof; it shows that (G2b) is an artefact
of the choice of the cell constants. -/
theorem gluing_lemma_without_doubling (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 Nb : ℕ) (Λ Cr : ℝ)
    {G P Pν : ℝ≥0∞} (hG : G ≠ ⊤) (hP : P ≠ ⊤) (hPν : Pν ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin n)) (R : ι → ℝ)
        (w v : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
        Continuous w → (∀ x, 0 ≤ w x) → Continuous v → (∀ j, 0 < s j) →
        closedBall x0 (2 * ρ) ⊆ ⋃ j, cube (c j) (s j) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ j, Real.sqrt n * s j ≤ ρ) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j, cubeNeighbor κ c s i j → cube (c i) (κ * s i) ⊆ ball (b j) (R j)) →
        (∀ j, R j ≤ Cr * s j) →
        (∀ j, ball (b j) (R j) ⊆ ball x0 (4 * ρ)) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ ball (b i) (R i)) → T.card ≤ Nb) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j))) →
        (∀ j, (volume.withDensity fun x => ENNReal.ofReal (v x)) (cube (c j) (s j)) ≤
          G * (volume.withDensity fun x => ENNReal.ofReal (w x)) (cube (c j) (s j))) →
        (∀ j, poincareAt volume w P 1 (b j) (R j)) →
        poincareAt volume v Pν 1 x0 (2 * ρ) →
        poincareAt volume w K 4 x0 ρ := by
  obtain ⟨K, hK, hcore⟩ := gluing_core.{u} n hκ N0 Nb Λ hG
    (A := 2 * (P * ENNReal.ofReal ((Cr * Λ) ^ 2))) (by finiteness) hPν
  refine ⟨K, hK, ?_⟩
  intro ι _ c s b R w v x0 ρ hw hw0 hv hs hcov hN0 hdiam hΛ hball hRs hin hNb hG1 hG2 hPj
    hν u hu
  have hκ0 : 0 ≤ κ := by linarith
  have hrefl : ∀ j, cubeNeighbor κ c s j j := fun j => cubeNeighbor_refl hκ0 (hs j).le
  have hR0 : ∀ j, 0 < R j := fun j =>
    pos_of_mem_ball (hball j j (hrefl j) (cube_center_mem (c j) (mul_nonneg hκ0 (hs j).le)))
  have huj : ∀ j, ContDiffOn ℝ 1 u (closedBall (b j) (R j)) := fun j =>
    hu.mono (gluing_closedBall_subset_of_ball_subset (hR0 j) (hin j))
  choose m hm using fun j => gluing_ball_minimizer hw hw0 (hPj j) (huj j)
  have hQB : ∀ i j, cubeNeighbor κ c s i j → cube (c j) (s j) ⊆ ball (b i) (R i) :=
    fun i j h => (cube_subset_enlarged (c j) hκ.le (hs j).le).trans
      (hball j i (cubeNeighbor_symm h))
  have hQ4 : ∀ j, cube (c j) (s j) ⊆ closedBall x0 (4 * ρ) := fun j =>
    ((hQB j j (hrefl j)).trans (hin j)).trans ball_subset_closedBall
  have H2 : ∀ i j, cubeNeighbor κ c s i j →
      ∫⁻ x in cube (c j) (s j), ENNReal.ofReal ((u x - m i) ^ 2) * ENNReal.ofReal (w x) ≤
        P * ENNReal.ofReal ((Cr * Λ) ^ 2) * ENNReal.ofReal (s j ^ 2) *
          ∫⁻ x in ball (b i) (R i),
            ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) * ENNReal.ofReal (w x) := by
    intro i j hij
    refine (lintegral_mono_set (hQB i j hij)).trans ((hm i).trans ?_)
    refine (mul_le_mul_right' (mul_le_mul_left'
      (gluing_radius_sq_le (hR0 i).le (hs i) (hRs i) (hΛ i j hij)) P) _).trans (le_of_eq ?_)
    ring
  refine hcore ι c s b R w v x0 ρ hw hv hs hcov hN0 hdiam hΛ hball hin hNb hG1 hG2 hν u m hu
    ?_ ?_
  · intro i j hij
    refine (H2 i j hij).trans ?_
    have h2 : P * ENNReal.ofReal ((Cr * Λ) ^ 2) ≤ 2 * (P * ENNReal.ofReal ((Cr * Λ) ^ 2)) := by
      rw [two_mul]
      exact le_self_add
    exact mul_le_mul_right' (mul_le_mul_right' h2 _) _
  · intro i j hij
    refine (gluing_cube_diff_le (cube_measurableSet _ _) hw (hu.continuousOn.mono (hQ4 j))
      (m i) (m j)).trans ?_
    refine (add_le_add (mul_le_mul_left' (H2 i j hij) 2)
      (mul_le_mul_left' (H2 j j (hrefl j)) 2)).trans (le_of_eq ?_)
    ring

end BrownRadial
