import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Partition of unity on a finite family of cubes

The proof of the gluing lemma (`lem:glue` of the paper) takes "a partition of
unity subordinate to the enlarged cubes with gradient at most a constant over
the side". This file constructs it and proves the bounds the proof uses.
There are no weights and no lattice here.

A cube is given by a centre and a side. The enlarged cube has the same centre
and side `κ * s`, with `κ > 1` a parameter (the paper takes `κ = 1.01`).

Contents.

* `cube` and its basic facts (closed, measurable, between two balls, volume).
* `cubeBump`: one smooth bump per cube, equal to one on the cube and to zero
  off the enlarged cube, with gradient at most `K / s` (`cubeBump_spec`).
* `cubePartitionFun`: the bump divided by the sum of the bumps of a finite
  family. The sum is at least one on every cube of the family, and that is
  where the gradient bounds are proved. Off the cubes the sum can be small
  and no gradient bound is claimed there.
* `cubePartitionCombination`: `∑ i, a i * ψ i` for constants `a i`.
* Volume counting: bounded overlap of the cubes and comparable sides of
  neighbours give bounded overlap of the enlarged cubes and a bounded number
  of neighbours.

Statements meant for the gluing lemma: `cubePartition_structure`,
`cubePartition_gradient_bounds`, `cubePartition_gradient_bounds_of_cube_overlap`,
`cube_enlarged_overlap_of_overlap`, `cubeNeighbors_exists_card_bound`, and the
single existence statement `cube_exists_partition_of_unity`. In each of them
every constant is quantified before the family of cubes.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal ContDiff Topology
namespace BrownRadial

universe u

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Cubes -/

/-- The closed axis-parallel cube with centre `c` and side `s`. -/
def cube (c : E) (s : ℝ) : Set E := {x | ∀ i, |x i - c i| ≤ s / 2}

theorem cube_mem_iff {c : E} {s : ℝ} {x : E} :
    x ∈ cube c s ↔ ∀ i, |x i - c i| ≤ s / 2 := Iff.rfl

theorem cube_isClosed (c : E) (s : ℝ) : IsClosed (cube c s) := by
  have h : cube c s = ⋂ i, {x : E | |x i - c i| ≤ s / 2} := by
    ext x
    simp [cube]
  rw [h]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact continuous_abs.comp (((EuclideanSpace.proj i).continuous).sub continuous_const)

theorem cube_measurableSet (c : E) (s : ℝ) : MeasurableSet (cube c s) :=
  (cube_isClosed c s).measurableSet

theorem cube_center_mem (c : E) {s : ℝ} (hs : 0 ≤ s) : c ∈ cube c s := by
  intro i
  rw [sub_self, abs_zero]
  exact div_nonneg hs zero_le_two

theorem cube_mono (c : E) {s t : ℝ} (hst : s ≤ t) : cube c s ⊆ cube c t := by
  intro x hx i
  exact (hx i).trans (by linarith)

/-- A cube lies in the Euclidean ball about its centre of radius half its
diameter `sqrt n * s`. -/
theorem cube_subset_closedBall (c : E) (s : ℝ) :
    cube c s ⊆ closedBall c (Real.sqrt n * s / 2) := by
  intro x hx
  rw [mem_closedBall, EuclideanSpace.dist_eq]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hs : 0 ≤ s / 2 := (abs_nonneg _).trans (hx ⟨0, hn⟩)
  have hsum : ∑ i, dist (x i) (c i) ^ 2 ≤ ∑ _i : Fin n, (s / 2) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrad : 0 ≤ Real.sqrt n * s / 2 := by
    have h0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hs
    linarith
  refine Real.sqrt_le_iff.mpr ⟨hrad, hsum.trans (le_of_eq ?_)⟩
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  calc (n : ℝ) * (s / 2) ^ 2 = Real.sqrt n ^ 2 * (s / 2) ^ 2 := by rw [hsq]
    _ = (Real.sqrt n * s / 2) ^ 2 := by ring

/-- A cube contains the Euclidean ball about its centre of radius half its side. -/
theorem cube_closedBall_subset (c : E) (s : ℝ) : closedBall c (s / 2) ⊆ cube c s := by
  intro x hx i
  rw [mem_closedBall, dist_eq_norm] at hx
  have h := PiLp.norm_apply_le (x - c) i
  rw [Real.norm_eq_abs] at h
  exact h.trans hx

/-- Lebesgue measure of a cube. -/
theorem cube_volume (c : E) {s : ℝ} (hs : 0 ≤ s) :
    volume (cube c s) = ENNReal.ofReal (s ^ n) := by
  have h : cube c s = (EuclideanSpace.measurableEquiv (Fin n)) ⁻¹'
      (Icc (fun i => c i - s / 2) (fun i => c i + s / 2)) := by
    ext x
    simp only [cube, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def, abs_le]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · change c i - s / 2 ≤ x i
        linarith [(h i).1]
      · change x i ≤ c i + s / 2
        linarith [(h i).2]
    · intro h i
      have h1 : c i - s / 2 ≤ x i := h.1 i
      have h2 : x i ≤ c i + s / 2 := h.2 i
      exact ⟨by linarith, by linarith⟩
  rw [h, (EuclideanSpace.volume_preserving_measurableEquiv (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  have h2 : ∀ i : Fin n, ENNReal.ofReal (c i + s / 2 - (c i - s / 2)) = ENNReal.ofReal s := by
    intro i
    congr 1
    ring
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hs]

/-! ## The one-dimensional step -/

/-- A smooth step: one on `t ≤ 0`, zero on `1 ≤ t`. -/
noncomputable def cubeStep (t : ℝ) : ℝ := Real.smoothTransition (1 - t)

theorem cubeStep_nonneg (t : ℝ) : 0 ≤ cubeStep t := Real.smoothTransition.nonneg _

theorem cubeStep_le_one (t : ℝ) : cubeStep t ≤ 1 := Real.smoothTransition.le_one _

theorem cubeStep_eq_one {t : ℝ} (ht : t ≤ 0) : cubeStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cubeStep_eq_zero {t : ℝ} (ht : 1 ≤ t) : cubeStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cubeStep_contDiff : ContDiff ℝ ∞ cubeStep :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- The derivative of the standard smooth transition vanishes off `[0, 1]`. -/
theorem cubeStep_deriv_smoothTransition_eq_zero {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]

/-- The only analytic input: the step is globally Lipschitz. -/
theorem cubeStep_exists_lipschitz :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u : ℝ, |cubeStep t - cubeStep u| ≤ M * |t - u| := by
  have hcd : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff (n := 1)
  have hd : Differentiable ℝ Real.smoothTransition := hcd.differentiable le_rfl
  have hc : Continuous (deriv Real.smoothTransition) := hcd.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hall : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · exact (hC t ht).trans (le_max_left _ _)
    · rw [cubeStep_deriv_smoothTransition_eq_zero ht, norm_zero]
      exact le_max_right _ _
  refine ⟨max C 0, le_max_right _ _, fun t u => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ)
    (fun x _ => hd.differentiableAt) (fun x _ => hall x) convex_univ
    (mem_univ (1 - u)) (mem_univ (1 - t))
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h2 : |1 - t - (1 - u)| = |t - u| := by
    rw [show 1 - t - (1 - u) = -(t - u) by ring, abs_neg]
  rw [h2] at h
  exact h

/-! ## The factor in one coordinate -/

/-- The profile in one coordinate: one on `|t - a| ≤ s / 2`, zero on
`κ * s / 2 < |t - a|`. -/
noncomputable def cubeFactor (κ s a t : ℝ) : ℝ :=
  cubeStep ((t - a - s / 2) / ((κ - 1) * s / 2)) * cubeStep ((a - t - s / 2) / ((κ - 1) * s / 2))

theorem cubeFactor_nonneg (κ s a t : ℝ) : 0 ≤ cubeFactor κ s a t :=
  mul_nonneg (cubeStep_nonneg _) (cubeStep_nonneg _)

theorem cubeFactor_le_one (κ s a t : ℝ) : cubeFactor κ s a t ≤ 1 :=
  mul_le_one₀ (cubeStep_le_one _) (cubeStep_nonneg _) (cubeStep_le_one _)

theorem cubeFactor_eq_one {κ s a t : ℝ} (hκ : 1 < κ) (hs : 0 < s) (ht : |t - a| ≤ s / 2) :
    cubeFactor κ s a t = 1 := by
  have hδ : 0 < (κ - 1) * s / 2 := by nlinarith
  rw [abs_le] at ht
  rw [cubeFactor, cubeStep_eq_one, cubeStep_eq_one, mul_one]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hδ.le
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hδ.le

theorem cubeFactor_eq_zero {κ s a t : ℝ} (hκ : 1 < κ) (hs : 0 < s) (ht : κ * s / 2 < |t - a|) :
    cubeFactor κ s a t = 0 := by
  have hδ : 0 < (κ - 1) * s / 2 := by nlinarith
  rw [cubeFactor]
  rcases lt_abs.mp ht with h | h
  · rw [cubeStep_eq_zero, zero_mul]
    rw [one_le_div hδ]
    linarith
  · rw [cubeStep_eq_zero (t := (a - t - s / 2) / ((κ - 1) * s / 2)), mul_zero]
    rw [one_le_div hδ]
    linarith

theorem cubeFactor_contDiff (κ s a : ℝ) : ContDiff ℝ ∞ (cubeFactor κ s a) := by
  unfold cubeFactor
  exact (cubeStep_contDiff.comp (((contDiff_id.sub contDiff_const).sub contDiff_const).div_const
    _)).mul (cubeStep_contDiff.comp (((contDiff_const.sub contDiff_id).sub
      contDiff_const).div_const _))

theorem cubeFactor_lipschitz {M : ℝ} (hM : ∀ t u : ℝ, |cubeStep t - cubeStep u| ≤ M * |t - u|)
    {κ s : ℝ} (hκ : 1 < κ) (hs : 0 < s) (a t u : ℝ) :
    |cubeFactor κ s a t - cubeFactor κ s a u| ≤ 4 * M / (κ - 1) / s * |t - u| := by
  have hδ : 0 < (κ - 1) * s / 2 := by nlinarith
  have hκ1 : 0 < κ - 1 := by linarith
  set p := cubeStep ((t - a - s / 2) / ((κ - 1) * s / 2)) with hp
  set q := cubeStep ((a - t - s / 2) / ((κ - 1) * s / 2)) with hq
  set p2 := cubeStep ((u - a - s / 2) / ((κ - 1) * s / 2)) with hp2
  set q2 := cubeStep ((a - u - s / 2) / ((κ - 1) * s / 2)) with hq2
  have h1 : |p - p2| ≤ M * (|t - u| / ((κ - 1) * s / 2)) := by
    refine (hM _ _).trans (le_of_eq ?_)
    rw [← sub_div, abs_div, abs_of_pos hδ]
    congr 3
    ring
  have h2 : |q - q2| ≤ M * (|t - u| / ((κ - 1) * s / 2)) := by
    refine (hM _ _).trans (le_of_eq ?_)
    rw [← sub_div, abs_div, abs_of_pos hδ]
    congr 2
    rw [show a - t - s / 2 - (a - u - s / 2) = -(t - u) by ring, abs_neg]
  have hpq : |p * q - p2 * q2| ≤ |p - p2| + |q - q2| := by
    have e : p * q - p2 * q2 = p * (q - q2) + (p - p2) * q2 := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have a1 : |p| ≤ 1 := by
      rw [abs_of_nonneg (cubeStep_nonneg _)]
      exact cubeStep_le_one _
    have a2 : |q2| ≤ 1 := by
      rw [abs_of_nonneg (cubeStep_nonneg _)]
      exact cubeStep_le_one _
    nlinarith [abs_nonneg (q - q2), abs_nonneg (p - p2)]
  have e : 4 * M / (κ - 1) / s * |t - u| =
      M * (|t - u| / ((κ - 1) * s / 2)) + M * (|t - u| / ((κ - 1) * s / 2)) := by
    field_simp
    ring
  rw [e]
  exact hpq.trans (add_le_add h1 h2)

/-! ## One bump per cube -/

/-- Products of numbers in `[0, 1]` differ by at most the sum of the differences. -/
theorem cube_abs_prod_sub_prod_le {α : Type*} (t : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i ∈ t, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ t, a i - ∏ i ∈ t, b i| ≤ ∑ i ∈ t, |a i - b i| := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert k t hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    have hak := ha k (Finset.mem_insert_self k t)
    have hB0 : 0 ≤ ∏ i ∈ t, b i :=
      Finset.prod_nonneg fun i hi => (hb i (Finset.mem_insert_of_mem hi)).1
    have hB1 : ∏ i ∈ t, b i ≤ 1 :=
      Finset.prod_le_one (fun i hi => (hb i (Finset.mem_insert_of_mem hi)).1)
        (fun i hi => (hb i (Finset.mem_insert_of_mem hi)).2)
    have ih2 := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have e : a k * ∏ i ∈ t, a i - b k * ∏ i ∈ t, b i =
        a k * (∏ i ∈ t, a i - ∏ i ∈ t, b i) + (a k - b k) * ∏ i ∈ t, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hak.1, abs_of_nonneg hB0]
    nlinarith [abs_nonneg (∏ i ∈ t, a i - ∏ i ∈ t, b i), abs_nonneg (a k - b k), hak.2]

/-- The bump of the cube with centre `c` and side `s`: the product over the
coordinates of the one-dimensional profile. It is one on the cube and zero
off the enlarged cube of side `κ * s`. -/
noncomputable def cubeBump (κ : ℝ) (c : E) (s : ℝ) (x : E) : ℝ :=
  ∏ i, cubeFactor κ s (c i) (x i)

theorem cubeBump_nonneg (κ : ℝ) (c : E) (s : ℝ) (x : E) : 0 ≤ cubeBump κ c s x :=
  Finset.prod_nonneg fun _ _ => cubeFactor_nonneg _ _ _ _

theorem cubeBump_le_one (κ : ℝ) (c : E) (s : ℝ) (x : E) : cubeBump κ c s x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cubeFactor_nonneg _ _ _ _) (fun _ _ => cubeFactor_le_one _ _ _ _)

theorem cubeBump_eq_one {κ s : ℝ} (hκ : 1 < κ) (hs : 0 < s) {c x : E} (hx : x ∈ cube c s) :
    cubeBump κ c s x = 1 :=
  Finset.prod_eq_one fun i _ => cubeFactor_eq_one hκ hs (hx i)

theorem cubeBump_eq_zero {κ s : ℝ} (hκ : 1 < κ) (hs : 0 < s) {c x : E}
    (hx : x ∉ cube c (κ * s)) : cubeBump κ c s x = 0 := by
  rw [cube_mem_iff, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (cubeFactor_eq_zero hκ hs (not_le.mp hi))

theorem cubeBump_contDiff (κ : ℝ) (c : E) (s : ℝ) : ContDiff ℝ ∞ (cubeBump κ c s) := by
  change ContDiff ℝ ∞ (fun x : E => ∏ i, cubeFactor κ s (c i) (x i))
  refine contDiff_prod fun i _ => ?_
  exact (cubeFactor_contDiff κ s (c i)).comp (contDiff_euclidean.mp contDiff_id i)

/-- The bump is Lipschitz with constant `K / s`, where `K` depends only on
the dimension and on `κ`. -/
theorem cubeBump_exists_lipschitz (n : ℕ) {κ : ℝ} (hκ : 1 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 < s →
      ∀ x y, |cubeBump κ c s x - cubeBump κ c s y| ≤ K / s * ‖x - y‖ := by
  obtain ⟨M, hM0, hM⟩ := cubeStep_exists_lipschitz
  have hκ1 : 0 < κ - 1 := by linarith
  refine ⟨n * (4 * M / (κ - 1)),
    mul_nonneg (Nat.cast_nonneg n) (div_nonneg (by linarith) hκ1.le), fun c s hs x y => ?_⟩
  have h1 := cube_abs_prod_sub_prod_le Finset.univ (fun i => cubeFactor κ s (c i) (x i))
    (fun i => cubeFactor κ s (c i) (y i))
    (fun i _ => ⟨cubeFactor_nonneg _ _ _ _, cubeFactor_le_one _ _ _ _⟩)
    (fun i _ => ⟨cubeFactor_nonneg _ _ _ _, cubeFactor_le_one _ _ _ _⟩)
  refine h1.trans ?_
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      |cubeFactor κ s (c i) (x i) - cubeFactor κ s (c i) (y i)| ≤
        4 * M / (κ - 1) / s * ‖x - y‖ := by
    intro i _
    refine (cubeFactor_lipschitz hM hκ hs (c i) (x i) (y i)).trans ?_
    have h3 : |x i - y i| ≤ ‖x - y‖ := by
      have h := PiLp.norm_apply_le (x - y) i
      rwa [Real.norm_eq_abs] at h
    exact mul_le_mul_of_nonneg_left h3
      (div_nonneg (div_nonneg (by linarith) hκ1.le) hs.le)
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The gradient of the bump is at most `K / s`, with `K` depending only on
the dimension and on `κ`. -/
theorem cubeBump_exists_fderiv_bound (n : ℕ) {κ : ℝ} (hκ : 1 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 < s →
      ∀ x, ‖fderiv ℝ (cubeBump κ c s) x‖ ≤ K / s := by
  obtain ⟨K, hK0, hK⟩ := cubeBump_exists_lipschitz n hκ
  refine ⟨K, hK0, fun c s hs x => ?_⟩
  have hnn : 0 ≤ K / s := div_nonneg hK0 hs.le
  have hlip : LipschitzWith (K / s).toNNReal (cubeBump κ c s) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hnn]
    exact hK c s hs y z
  have h := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
  rwa [Real.coe_toNNReal _ hnn] at h

/-- Target 2 in one statement: one bump per cube, with the gradient constant
chosen before the cube. -/
theorem cubeBump_spec (n : ℕ) {κ : ℝ} (hκ : 1 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 < s →
      ContDiff ℝ ∞ (cubeBump κ c s) ∧
      (∀ x, 0 ≤ cubeBump κ c s x) ∧
      (∀ x, cubeBump κ c s x ≤ 1) ∧
      (∀ x ∈ cube c s, cubeBump κ c s x = 1) ∧
      (∀ x, x ∉ cube c (κ * s) → cubeBump κ c s x = 0) ∧
      ∀ x, ‖fderiv ℝ (cubeBump κ c s) x‖ ≤ K / s := by
  obtain ⟨K, hK0, hK⟩ := cubeBump_exists_fderiv_bound n hκ
  exact ⟨K, hK0, fun c s hs => ⟨cubeBump_contDiff κ c s, cubeBump_nonneg κ c s,
    cubeBump_le_one κ c s, fun _ hx => cubeBump_eq_one hκ hs hx,
    fun _ hx => cubeBump_eq_zero hκ hs hx, hK c s hs⟩⟩

/-- A function that vanishes off a closed cube has zero derivative off it. -/
theorem cube_fderiv_eq_zero_of_notMem {f : E → ℝ} {c : E} {t : ℝ}
    (hf : ∀ y, y ∉ cube c t → f y = 0) {x : E} (hx : x ∉ cube c t) : fderiv ℝ f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(cube_isClosed c t).isOpen_compl.mem_nhds hx] with y hy
    exact hf y hy
  rw [h.fderiv_eq]
  simp

theorem cube_subset_enlarged (c : E) {κ s : ℝ} (hκ : 1 ≤ κ) (hs : 0 ≤ s) :
    cube c s ⊆ cube c (κ * s) :=
  cube_mono c (by nlinarith)

/-! ## The partition of unity -/

section Partition

variable {ι : Type*} [Fintype ι]

/-- The sum of the bumps of a finite family of cubes. -/
noncomputable def cubePartitionSum (κ : ℝ) (c : ι → E) (s : ι → ℝ) (x : E) : ℝ :=
  ∑ i, cubeBump κ (c i) (s i) x

/-- The open set on which the partition lives: where the sum of the bumps is
positive. It contains every cube of the family. -/
def cubePartitionDomain (κ : ℝ) (c : ι → E) (s : ι → ℝ) : Set E :=
  {x | 0 < cubePartitionSum κ c s x}

/-- The member of the partition attached to the cube `j`. Off the domain it
is zero (division by zero). -/
noncomputable def cubePartitionFun (κ : ℝ) (c : ι → E) (s : ι → ℝ) (j : ι) (x : E) : ℝ :=
  cubeBump κ (c j) (s j) x / cubePartitionSum κ c s x

/-- The combination `∑ i, a i * ψ i` of constants: the function `U` of the
paper's proof when `a i` is the mean of `u` on the cube `i`. -/
noncomputable def cubePartitionCombination (κ : ℝ) (c : ι → E) (s : ι → ℝ) (a : ι → ℝ)
    (x : E) : ℝ :=
  ∑ i, a i * cubePartitionFun κ c s i x

/-- The paper's relation `i ∼ j`: the enlarged cubes meet. -/
def cubeNeighbor (κ : ℝ) (c : ι → E) (s : ι → ℝ) (i j : ι) : Prop :=
  (cube (c i) (κ * s i) ∩ cube (c j) (κ * s j)).Nonempty

/-- The indices `i` with `i ∼ j`. -/
noncomputable def cubeNeighbors (κ : ℝ) (c : ι → E) (s : ι → ℝ) (j : ι) : Finset ι :=
  haveI := Classical.decPred fun i => cubeNeighbor κ c s i j
  Finset.univ.filter fun i => cubeNeighbor κ c s i j

variable {κ : ℝ} {c : ι → EuclideanSpace ℝ (Fin n)} {s : ι → ℝ}

theorem cubeNeighbors_mem_iff {i j : ι} :
    i ∈ cubeNeighbors κ c s j ↔ cubeNeighbor κ c s i j := by
  simp [cubeNeighbors]

omit [Fintype ι] in
theorem cubeNeighbor_symm {i j : ι} (h : cubeNeighbor κ c s i j) : cubeNeighbor κ c s j i := by
  rwa [cubeNeighbor, inter_comm]

omit [Fintype ι] in
theorem cubeNeighbor_refl (hκ : 0 ≤ κ) {j : ι} (hs : 0 ≤ s j) : cubeNeighbor κ c s j j :=
  ⟨c j, cube_center_mem _ (mul_nonneg hκ hs), cube_center_mem _ (mul_nonneg hκ hs)⟩

theorem cubePartitionSum_contDiff : ContDiff ℝ ∞ (cubePartitionSum κ c s) := by
  change ContDiff ℝ ∞ (fun x => ∑ i, cubeBump κ (c i) (s i) x)
  exact ContDiff.sum fun i _ => cubeBump_contDiff κ (c i) (s i)

theorem cubePartitionSum_nonneg (x : E) : 0 ≤ cubePartitionSum κ c s x :=
  Finset.sum_nonneg fun _ _ => cubeBump_nonneg _ _ _ _

theorem cubeBump_le_cubePartitionSum (j : ι) (x : E) :
    cubeBump κ (c j) (s j) x ≤ cubePartitionSum κ c s x :=
  Finset.single_le_sum (f := fun i => cubeBump κ (c i) (s i) x)
    (fun _ _ => cubeBump_nonneg _ _ _ _) (Finset.mem_univ j)

/-- On each cube of the family the sum of the bumps is at least one. This is
what keeps the gradients of the quotients under control there. -/
theorem cubePartitionSum_one_le (hκ : 1 < κ) (hs : ∀ i, 0 < s i) {j : ι} {x : E}
    (hx : x ∈ cube (c j) (s j)) : 1 ≤ cubePartitionSum κ c s x := by
  rw [← cubeBump_eq_one hκ (hs j) hx]
  exact cubeBump_le_cubePartitionSum j x

theorem cubePartitionDomain_isOpen : IsOpen (cubePartitionDomain κ c s) :=
  isOpen_lt continuous_const cubePartitionSum_contDiff.continuous

theorem cubePartitionDomain_cube_subset (hκ : 1 < κ) (hs : ∀ i, 0 < s i) (j : ι) :
    cube (c j) (s j) ⊆ cubePartitionDomain κ c s :=
  fun _ hx => lt_of_lt_of_le one_pos (cubePartitionSum_one_le hκ hs hx)

theorem cubePartitionDomain_subset (hκ : 1 < κ) (hs : ∀ i, 0 < s i) :
    cubePartitionDomain κ c s ⊆ ⋃ j, cube (c j) (κ * s j) := by
  intro x hx
  by_contra hne
  rw [mem_iUnion, not_exists] at hne
  have h0 : cubePartitionSum κ c s x = 0 :=
    Finset.sum_eq_zero fun i _ => cubeBump_eq_zero hκ (hs i) (hne i)
  have hx2 : 0 < cubePartitionSum κ c s x := hx
  rw [h0] at hx2
  exact lt_irrefl _ hx2

theorem cubePartitionFun_contDiffAt (j : ι) {x : E} (hx : x ∈ cubePartitionDomain κ c s) :
    ContDiffAt ℝ ∞ (cubePartitionFun κ c s j) x := by
  change ContDiffAt ℝ ∞ (fun y => cubeBump κ (c j) (s j) y / cubePartitionSum κ c s y) x
  exact (cubeBump_contDiff _ _ _).contDiffAt.div cubePartitionSum_contDiff.contDiffAt
    (ne_of_gt hx)

theorem cubePartitionFun_contDiffOn (j : ι) :
    ContDiffOn ℝ ∞ (cubePartitionFun κ c s j) (cubePartitionDomain κ c s) :=
  fun _ hx => (cubePartitionFun_contDiffAt j hx).contDiffWithinAt

theorem cubePartitionFun_differentiableAt (j : ι) {x : E}
    (hx : x ∈ cubePartitionDomain κ c s) :
    DifferentiableAt ℝ (cubePartitionFun κ c s j) x :=
  (cubePartitionFun_contDiffAt j hx).differentiableAt (by simp)

theorem cubePartitionFun_nonneg (j : ι) (x : E) : 0 ≤ cubePartitionFun κ c s j x :=
  div_nonneg (cubeBump_nonneg _ _ _ _) (cubePartitionSum_nonneg x)

theorem cubePartitionFun_le_one (j : ι) (x : E) : cubePartitionFun κ c s j x ≤ 1 :=
  div_le_one_of_le₀ (cubeBump_le_cubePartitionSum j x) (cubePartitionSum_nonneg x)

theorem cubePartitionFun_sum_eq_one {x : E} (hx : x ∈ cubePartitionDomain κ c s) :
    ∑ j, cubePartitionFun κ c s j x = 1 := by
  have h : ∑ j, cubePartitionFun κ c s j x =
      cubePartitionSum κ c s x / cubePartitionSum κ c s x := by
    unfold cubePartitionFun
    rw [← Finset.sum_div]
    rfl
  rw [h]
  exact div_self (ne_of_gt hx)

theorem cubePartitionFun_eq_zero (hκ : 1 < κ) {j : ι} (hs : 0 < s j) {x : E}
    (hx : x ∉ cube (c j) (κ * s j)) : cubePartitionFun κ c s j x = 0 := by
  rw [cubePartitionFun, cubeBump_eq_zero hκ hs hx, zero_div]

theorem cubePartitionFun_fderiv_eq_zero (hκ : 1 < κ) {j : ι} (hs : 0 < s j) {x : E}
    (hx : x ∉ cube (c j) (κ * s j)) : fderiv ℝ (cubePartitionFun κ c s j) x = 0 :=
  cube_fderiv_eq_zero_of_notMem (f := cubePartitionFun κ c s j) (c := c j) (t := κ * s j)
    (fun _ hy => cubePartitionFun_eq_zero hκ hs hy) hx

theorem cubePartitionSum_differentiableAt (x : E) :
    DifferentiableAt ℝ (cubePartitionSum κ c s) x :=
  (cubePartitionSum_contDiff.differentiable (by simp)).differentiableAt

/-! ### Gradient bounds on the cubes of the family -/

/-- Quotient rule, in the form used: on a cube of the family the sum of the
bumps is at least one, so the gradient of a member of the partition is at
most the gradient of its bump plus the gradient of the sum. -/
theorem cubePartitionFun_fderiv_le (hκ : 1 < κ) (hs : ∀ i, 0 < s i) (i : ι) {j : ι} {x : E}
    (hx : x ∈ cube (c j) (s j)) :
    ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤
      ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ + ‖fderiv ℝ (cubePartitionSum κ c s) x‖ := by
  have hxU := cubePartitionDomain_cube_subset hκ hs j hx
  have hS1 := cubePartitionSum_one_le hκ hs hx
  have hdψ := cubePartitionFun_differentiableAt (κ := κ) (c := c) (s := s) i hxU
  have hdS := cubePartitionSum_differentiableAt (κ := κ) (c := c) (s := s) x
  have heq : (fun y => cubePartitionFun κ c s i y * cubePartitionSum κ c s y) =ᶠ[𝓝 x]
      cubeBump κ (c i) (s i) := by
    filter_upwards [cubePartitionDomain_isOpen.mem_nhds hxU] with y hy
    exact div_mul_cancel₀ _ (ne_of_gt hy)
  have h1 := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_mul hdψ hdS] at h1
  have h2 : cubePartitionSum κ c s x • fderiv ℝ (cubePartitionFun κ c s i) x =
      fderiv ℝ (cubeBump κ (c i) (s i)) x -
        cubePartitionFun κ c s i x • fderiv ℝ (cubePartitionSum κ c s) x := by
    rw [← h1]
    abel
  calc ‖fderiv ℝ (cubePartitionFun κ c s i) x‖
      ≤ cubePartitionSum κ c s x * ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hS1
    _ = ‖cubePartitionSum κ c s x • fderiv ℝ (cubePartitionFun κ c s i) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (cubePartitionSum_nonneg x)]
    _ = ‖fderiv ℝ (cubeBump κ (c i) (s i)) x -
          cubePartitionFun κ c s i x • fderiv ℝ (cubePartitionSum κ c s) x‖ := by rw [h2]
    _ ≤ ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ +
          ‖cubePartitionFun κ c s i x • fderiv ℝ (cubePartitionSum κ c s) x‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ + ‖fderiv ℝ (cubePartitionSum κ c s) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (cubePartitionFun_nonneg i x)]
        exact add_le_add_left
          (mul_le_of_le_one_left (norm_nonneg _) (cubePartitionFun_le_one i x)) _

omit [Fintype ι] in
/-- At a point of the cube `j`, every bump of the family has gradient at most
`K0 * Λ / s j`: the bumps whose enlarged cube does not contain the point have
zero gradient there, and the others belong to neighbours of `j`. -/
theorem cubeBump_fderiv_le_on_cube (hκ : 1 < κ) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hs : ∀ i, 0 < s i)
    (hb : ∀ i x, ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ ≤ K0 / s i)
    {Λ : ℝ} (hΛ : ∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j)
    (i : ι) {j : ι} {x : E} (hx : x ∈ cube (c j) (s j)) :
    ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ ≤ K0 * Λ / s j := by
  have hκ0 : 0 ≤ κ := by linarith
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ j j (cubeNeighbor_refl hκ0 (hs j).le)
    exact le_of_mul_le_mul_right (by linarith) (hs j)
  by_cases hxi : x ∈ cube (c i) (κ * s i)
  · have h1 := hΛ j i ⟨x, cube_subset_enlarged (c j) hκ.le (hs j).le hx, hxi⟩
    refine (hb i x).trans ?_
    rw [div_le_div_iff₀ (hs i) (hs j)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hK0]
  · rw [cube_fderiv_eq_zero_of_notMem (fun y hy => cubeBump_eq_zero hκ (hs i) hy) hxi,
      norm_zero]
    exact div_nonneg (mul_nonneg hK0 (by linarith)) (hs j).le

/-- At a point of the cube `j`, the gradient of the sum of the bumps is at
most `N * (K0 * Λ / s j)` when the point lies in at most `N` enlarged cubes. -/
theorem cubePartitionSum_fderiv_le (hκ : 1 < κ) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hs : ∀ i, 0 < s i)
    (hb : ∀ i x, ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ ≤ K0 / s i)
    {Λ : ℝ} (hΛ : ∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j)
    {N : ℕ} (hN : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N)
    {j : ι} {x : E} (hx : x ∈ cube (c j) (s j)) :
    ‖fderiv ℝ (cubePartitionSum κ c s) x‖ ≤ N * (K0 * Λ / s j) := by
  classical
  have hfd : fderiv ℝ (cubePartitionSum κ c s) x =
      ∑ i, fderiv ℝ (cubeBump κ (c i) (s i)) x := by
    change fderiv ℝ (fun y => ∑ i, cubeBump κ (c i) (s i) y) x = _
    exact fderiv_fun_sum fun i _ =>
      ((cubeBump_contDiff κ (c i) (s i)).differentiable (by simp)).differentiableAt
  rw [hfd]
  have hzero : ∀ i ∈ (Finset.univ : Finset ι),
      i ∉ Finset.univ.filter (fun i => x ∈ cube (c i) (κ * s i)) →
      fderiv ℝ (cubeBump κ (c i) (s i)) x = 0 := by
    intro i _ hi
    have hxi : x ∉ cube (c i) (κ * s i) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    exact cube_fderiv_eq_zero_of_notMem (fun y hy => cubeBump_eq_zero hκ (hs i) hy) hxi
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (K0 * Λ / s j) fun i _ =>
    cubeBump_fderiv_le_on_cube hκ hK0 hs hb hΛ i hx).trans ?_
  rw [nsmul_eq_mul]
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ j j (cubeNeighbor_refl (by linarith) (hs j).le)
    exact le_of_mul_le_mul_right (by linarith) (hs j)
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (mul_nonneg hK0 (by linarith)) (hs j).le)
  exact Nat.cast_le.mpr (hN x _ fun i hi => (Finset.mem_filter.mp hi).2)

/-- **Gradient bound for the partition.** The constant is chosen before the
family of cubes: it depends only on the dimension, on `κ`, on the overlap
bound `N` of the enlarged cubes and on the ratio `Λ` of the sides of
neighbouring cubes. -/
theorem cubePartitionFun_exists_fderiv_bound (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N : ℕ) (Λ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        ∀ i j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤ K / s j := by
  obtain ⟨K0, hK0, hb⟩ := cubeBump_exists_fderiv_bound n hκ
  refine ⟨(N + 1) * (K0 * |Λ|),
    mul_nonneg (by positivity) (mul_nonneg hK0 (abs_nonneg _)), ?_⟩
  intro ι _ c s hs hN hΛ i j x hx
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ j j (cubeNeighbor_refl (by linarith) (hs j).le)
    exact le_of_mul_le_mul_right (by linarith) (hs j)
  rw [abs_of_nonneg (by linarith)]
  have hb2 : ∀ i x, ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ ≤ K0 / s i :=
    fun i x => hb (c i) (s i) (hs i) x
  calc ‖fderiv ℝ (cubePartitionFun κ c s i) x‖
      ≤ ‖fderiv ℝ (cubeBump κ (c i) (s i)) x‖ + ‖fderiv ℝ (cubePartitionSum κ c s) x‖ :=
        cubePartitionFun_fderiv_le hκ hs i hx
    _ ≤ K0 * Λ / s j + N * (K0 * Λ / s j) :=
        add_le_add (cubeBump_fderiv_le_on_cube hκ hK0 hs hb2 hΛ i hx)
          (cubePartitionSum_fderiv_le hκ hK0 hs hb2 hΛ hN hx)
    _ = (N + 1) * (K0 * Λ) / s j := by ring

/-- The paper's literal bound, gradient of `ψ i` against the side of its own
cube `i`, on the union of the cubes of the family. -/
theorem cubePartitionFun_exists_fderiv_bound_own_side (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N : ℕ)
    (Λ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        ∀ i x, x ∈ ⋃ j, cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤ K / s i := by
  obtain ⟨K1, hK1, h⟩ := cubePartitionFun_exists_fderiv_bound.{u} n hκ N Λ
  refine ⟨K1 * |Λ|, mul_nonneg hK1 (abs_nonneg _), ?_⟩
  intro ι _ c s hs hN hΛ i x hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ j j (cubeNeighbor_refl (by linarith) (hs j).le)
    exact le_of_mul_le_mul_right (by linarith) (hs j)
  rw [abs_of_nonneg (by linarith)]
  by_cases hxi : x ∈ cube (c i) (κ * s i)
  · have h1 := hΛ i j ⟨x, hxi, cube_subset_enlarged (c j) hκ.le (hs j).le hxj⟩
    refine (h ι c s hs hN hΛ i j x hxj).trans ?_
    rw [div_le_div_iff₀ (hs j) (hs i)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hK1]
  · rw [cubePartitionFun_fderiv_eq_zero hκ (hs i) hxi, norm_zero]
    exact div_nonneg (mul_nonneg hK1 (by linarith)) (hs i).le

/-! ### Combinations of constants -/

/-- The gradients of the members of the partition sum to zero on the domain. -/
theorem cubePartitionFun_sum_fderiv_eq_zero {x : E} (hx : x ∈ cubePartitionDomain κ c s) :
    ∑ i, fderiv ℝ (cubePartitionFun κ c s i) x = 0 := by
  have h : (fun y => ∑ i, cubePartitionFun κ c s i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [cubePartitionDomain_isOpen.mem_nhds hx] with y hy
    exact cubePartitionFun_sum_eq_one hy
  have h1 := h.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_sum (fun i _ => cubePartitionFun_differentiableAt i hx)] at h1
  rw [h1]
  simp

theorem cubePartitionCombination_fderiv_eq (a : ι → ℝ) (j : ι) {x : E}
    (hx : x ∈ cubePartitionDomain κ c s) :
    fderiv ℝ (cubePartitionCombination κ c s a) x =
      ∑ i, (a i - a j) • fderiv ℝ (cubePartitionFun κ c s i) x := by
  have h1 : fderiv ℝ (cubePartitionCombination κ c s a) x =
      ∑ i, a i • fderiv ℝ (cubePartitionFun κ c s i) x := by
    change fderiv ℝ (fun y => ∑ i, a i * cubePartitionFun κ c s i y) x = _
    rw [fderiv_fun_sum (fun i _ => (cubePartitionFun_differentiableAt i hx).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ =>
      fderiv_const_mul (cubePartitionFun_differentiableAt i hx) (a i)
  rw [h1]
  simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
    cubePartitionFun_sum_fderiv_eq_zero hx, smul_zero, sub_zero]

/-- The gradient of a combination of constants at a point of the cube `j`,
given a bound `B` for the gradients of the members of the partition there. -/
theorem cubePartitionCombination_fderiv_sq_le (hκ : 1 < κ) (hs : ∀ i, 0 < s i)
    {N : ℕ} (hN : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N)
    {B : ℝ} (a : ι → ℝ) {j : ι} {x : E} (hx : x ∈ cube (c j) (s j))
    (hψ : ∀ i, ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤ B) :
    ‖fderiv ℝ (cubePartitionCombination κ c s a) x‖ ^ 2 ≤
      N * B ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2 := by
  classical
  have hxU := cubePartitionDomain_cube_subset hκ hs j hx
  rw [cubePartitionCombination_fderiv_eq a j hxU]
  have hzero : ∀ i ∈ (Finset.univ : Finset ι),
      i ∉ Finset.univ.filter (fun i => x ∈ cube (c i) (κ * s i)) →
      (a i - a j) • fderiv ℝ (cubePartitionFun κ c s i) x = 0 := by
    intro i _ hi
    have hxi : x ∉ cube (c i) (κ * s i) :=
      fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    rw [cubePartitionFun_fderiv_eq_zero hκ (hs i) hxi, smul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  set T := Finset.univ.filter (fun i => x ∈ cube (c i) (κ * s i)) with hT
  have h1 : ‖∑ i ∈ T, (a i - a j) • fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤
      B * ∑ i ∈ T, |a i - a j| := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hψ i) (abs_nonneg _)
  have hTsub : T ⊆ cubeNeighbors κ c s j := by
    intro i hi
    rw [cubeNeighbors_mem_iff]
    exact ⟨x, (Finset.mem_filter.mp hi).2, cube_subset_enlarged (c j) hκ.le (hs j).le hx⟩
  have hcard : (T.card : ℝ) ≤ N := by
    exact_mod_cast hN x T (fun i hi => (Finset.mem_filter.mp hi).2)
  have h2 : (∑ i ∈ T, |a i - a j|) ^ 2 ≤ T.card * ∑ i ∈ T, |a i - a j| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ i ∈ T, |a i - a j| ^ 2 ≤ ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2 := by
    simp only [sq_abs]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => sq_nonneg _)
  have h4 : (0 : ℝ) ≤ ∑ i ∈ T, |a i - a j| ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ‖∑ i ∈ T, (a i - a j) • fderiv ℝ (cubePartitionFun κ c s i) x‖ ^ 2
      ≤ (B * ∑ i ∈ T, |a i - a j|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = B ^ 2 * (∑ i ∈ T, |a i - a j|) ^ 2 := by ring
    _ ≤ B ^ 2 * (T.card * ∑ i ∈ T, |a i - a j| ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg B)
    _ ≤ B ^ 2 * (N * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hcard h3 h4 (Nat.cast_nonneg N)) (sq_nonneg B)
    _ = N * B ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2 := by ring

/-- **The form used in the paper.** For constants `a i` and
`U = ∑ i, a i * ψ i`, at every point of the cube `j`,
`|∇U|² ≤ K / s j² * ∑_{i ∼ j} (a i - a j)²`, with `K` chosen before the
family of cubes. -/
theorem cubePartitionCombination_exists_fderiv_bound (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N : ℕ)
    (Λ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        ∀ (a : ι → ℝ) j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionCombination κ c s a) x‖ ^ 2 ≤
            K / s j ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2 := by
  obtain ⟨K1, hK1, h⟩ := cubePartitionFun_exists_fderiv_bound.{u} n hκ N Λ
  refine ⟨N * K1 ^ 2, mul_nonneg (Nat.cast_nonneg N) (sq_nonneg K1), ?_⟩
  intro ι _ c s hs hN hΛ a j x hx
  have h1 := cubePartitionCombination_fderiv_sq_le hκ hs hN (B := K1 / s j)
    a hx (fun i => h ι c s hs hN hΛ i j x hx)
  refine h1.trans (le_of_eq ?_)
  rw [div_pow]
  ring

/-- On the cube `j`, for any number `t`:
`|t - U| ≤ ∑_{i ∼ j} ψ i * |t - a i|`. With `t = u x` this is the paper's
`|u - U| ≤ ∑_{j' ∼ j} ψ_{j'} |u - ū_{j'}|`. No overlap hypothesis is needed. -/
theorem cubePartitionCombination_sub_le_weighted (hκ : 1 < κ) (hs : ∀ i, 0 < s i)
    (a : ι → ℝ) (t : ℝ) {j : ι} {x : E} (hx : x ∈ cube (c j) (s j)) :
    |t - cubePartitionCombination κ c s a x| ≤
      ∑ i ∈ cubeNeighbors κ c s j, cubePartitionFun κ c s i x * |t - a i| := by
  have hxU := cubePartitionDomain_cube_subset hκ hs j hx
  have hsum := cubePartitionFun_sum_eq_one hxU
  have e : t - cubePartitionCombination κ c s a x =
      ∑ i, cubePartitionFun κ c s i x * (t - a i) := by
    unfold cubePartitionCombination
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  have habs : ∀ i, |cubePartitionFun κ c s i x * (t - a i)| =
      cubePartitionFun κ c s i x * |t - a i| :=
    fun i => by rw [abs_mul, abs_of_nonneg (cubePartitionFun_nonneg i x)]
  simp only [habs]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hxi : x ∉ cube (c i) (κ * s i) := fun h =>
    hi (cubeNeighbors_mem_iff.mpr ⟨x, h, cube_subset_enlarged (c j) hκ.le (hs j).le hx⟩)
  rw [cubePartitionFun_eq_zero hκ (hs i) hxi, zero_mul]

/-- On the cube `j`: `|U - a j| ≤ ∑_{i ∼ j} |a i - a j|`. -/
theorem cubePartitionCombination_sub_le (hκ : 1 < κ) (hs : ∀ i, 0 < s i)
    (a : ι → ℝ) {j : ι} {x : E} (hx : x ∈ cube (c j) (s j)) :
    |cubePartitionCombination κ c s a x - a j| ≤
      ∑ i ∈ cubeNeighbors κ c s j, |a i - a j| := by
  have h := cubePartitionCombination_sub_le_weighted hκ hs a (a j) hx
  rw [abs_sub_comm]
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_sub_comm]
  exact mul_le_of_le_one_left (abs_nonneg _) (cubePartitionFun_le_one i x)

/-! ### Smoothness of combinations (target 4) -/

theorem cubePartitionCombination_contDiffAt (a : ι → ℝ) {x : E}
    (hx : x ∈ cubePartitionDomain κ c s) :
    ContDiffAt ℝ ∞ (cubePartitionCombination κ c s a) x := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, a i * cubePartitionFun κ c s i y) x
  exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (cubePartitionFun_contDiffAt i hx)

theorem cubePartitionCombination_contDiffOn (a : ι → ℝ) :
    ContDiffOn ℝ ∞ (cubePartitionCombination κ c s a) (cubePartitionDomain κ c s) :=
  fun _ hx => (cubePartitionCombination_contDiffAt a hx).contDiffWithinAt

/-- A combination of constants is `C¹` (indeed smooth) on every set contained
in the union of the cubes of the family; the set need not be closed. -/
theorem cubePartitionCombination_contDiffOn_one (hκ : 1 < κ) (hs : ∀ i, 0 < s i)
    (a : ι → ℝ) {F : Set E} (hF : F ⊆ ⋃ j, cube (c j) (s j)) :
    ContDiffOn ℝ 1 (cubePartitionCombination κ c s a) F :=
  ((cubePartitionCombination_contDiffOn a).of_le (by simp)).mono
    (hF.trans (iUnion_subset fun j => cubePartitionDomain_cube_subset hκ hs j))

end Partition

/-! ## Overlap of the enlarged cubes from overlap of the cubes

The paper assumes bounded overlap of the cubes themselves. The gradient
bounds need bounded overlap of the enlarged cubes. With comparable sides of
neighbours the second follows from the first by counting volume. -/

/-- If no point lies in more than `N0` of the cubes, the volumes of any of
them that lie in a common cube add up to at most `N0` times its volume. -/
theorem cube_sum_volume_le {ι : Type*} (T : Finset ι) (c : ι → E) (s : ι → ℝ) (N0 : ℕ)
    (hN0 : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0)
    (b : E) (r : ℝ) (hsub : ∀ i ∈ T, cube (c i) (s i) ⊆ cube b r) :
    ∑ i ∈ T, volume (cube (c i) (s i)) ≤ N0 * volume (cube b r) := by
  classical
  have h1 : ∑ i ∈ T, volume (cube (c i) (s i)) =
      ∫⁻ y, ∑ i ∈ T, (cube (c i) (s i)).indicator (1 : E → ℝ≥0∞) y := by
    rw [lintegral_finset_sum T fun i _ => measurable_one.indicator (cube_measurableSet _ _)]
    exact Finset.sum_congr rfl fun i _ =>
      (lintegral_indicator_one (cube_measurableSet _ _)).symm
  rw [h1, ← lintegral_indicator_const (cube_measurableSet b r)]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ cube b r
  · rw [indicator_of_mem hy]
    have h2 : ∑ i ∈ T, (cube (c i) (s i)).indicator (1 : E → ℝ≥0∞) y =
        ((T.filter fun i => y ∈ cube (c i) (s i)).card : ℝ≥0∞) := by
      simp [indicator_apply, Finset.sum_boole]
    rw [h2]
    exact_mod_cast hN0 y _ (fun i hi => (Finset.mem_filter.mp hi).2)
  · rw [indicator_of_notMem hy]
    refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
    exact indicator_of_notMem (fun h => hy (hsub i hi h)) _

/-- Counting by volume: cubes of the family with sides at least `σ`, inside
a common cube of side `r`, number at most `N0 * (r / σ) ^ n`. -/
theorem cube_card_mul_pow_le {ι : Type*} (T : Finset ι) (c : ι → E) (s : ι → ℝ) (N0 : ℕ)
    (hN0 : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0)
    (b : E) {r : ℝ} (hr : 0 ≤ r) (hsub : ∀ i ∈ T, cube (c i) (s i) ⊆ cube b r)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσs : ∀ i ∈ T, σ ≤ s i) :
    (T.card : ℝ) * σ ^ n ≤ N0 * r ^ n := by
  have hvol := cube_sum_volume_le T c s N0 hN0 b r hsub
  have hlow : (T.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ n) ≤
      ∑ i ∈ T, volume (cube (c i) (s i)) := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun i hi => ?_
    rw [cube_volume _ (hσ.trans (hσs i hi))]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hσ (hσs i hi) n)
  rw [cube_volume _ hr] at hvol
  have h6 : ENNReal.ofReal (T.card * σ ^ n) ≤ ENNReal.ofReal (N0 * r ^ n) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    exact hlow.trans hvol
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h6

/-- Volume count: a point lies in at most `N0 * (2 * κ * Λ ^ 2) ^ n` of the
enlarged cubes. -/
theorem cube_enlarged_overlap_card_le {ι : Type*} {κ : ℝ} (hκ : 1 < κ) {c : ι → E}
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {N0 : ℕ}
    (hN0 : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0)
    {Λ : ℝ} (hΛ : ∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j)
    (x : E) (T : Finset ι) (hT : ∀ i ∈ T, x ∈ cube (c i) (κ * s i)) :
    (T.card : ℝ) ≤ N0 * (2 * κ * Λ ^ 2) ^ n := by
  have hκ0 : 0 < κ := by linarith
  rcases T.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hσ0 : 0 < s i0 := hs i0
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ i0 i0 (cubeNeighbor_refl hκ0.le hσ0.le)
    exact le_of_mul_le_mul_right (by linarith) hσ0
  have hΛ0 : 0 < Λ := by linarith
  have hup : ∀ i ∈ T, s i ≤ Λ * s i0 := fun i hi => hΛ i i0 ⟨x, hT i hi, hT i0 hi0⟩
  have hlo : ∀ i ∈ T, s i0 ≤ Λ * s i := fun i hi => hΛ i0 i ⟨x, hT i0 hi0, hT i hi⟩
  have hsub : ∀ i ∈ T, cube (c i) (s i) ⊆ cube x (2 * κ * Λ * s i0) := by
    intro i hi y hy k
    have h1 : |y k - c i k| ≤ s i / 2 := hy k
    have h2 : |x k - c i k| ≤ κ * s i / 2 := hT i hi k
    have h3 : |y k - x k| ≤ |y k - c i k| + |x k - c i k| := by
      have h := abs_sub_le (y k) (c i k) (x k)
      rwa [abs_sub_comm (c i k) (x k)] at h
    have h4 : κ * s i ≤ κ * (Λ * s i0) := mul_le_mul_of_nonneg_left (hup i hi) hκ0.le
    nlinarith [hs i, mul_pos hκ0 (hs i)]
  have hbig : 0 ≤ 2 * κ * Λ * s i0 := by positivity
  have h7 := cube_card_mul_pow_le T c s N0 hN0 x hbig hsub (σ := s i0 / Λ) (by positivity)
    (fun i hi => by
      rw [div_le_iff₀ hΛ0]
      linarith [hlo i hi])
  have h8 : (2 * κ * Λ * s i0) ^ n = (2 * κ * Λ ^ 2) ^ n * (s i0 / Λ) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h8, ← mul_assoc] at h7
  exact le_of_mul_le_mul_right h7 (by positivity)

/-- **Bounded overlap of the cubes gives bounded overlap of the enlarged
cubes**, with a bound chosen before the family: it depends only on the
dimension, `κ`, the overlap bound `N0` of the cubes and the side ratio `Λ`. -/
theorem cube_enlarged_overlap_of_overlap (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 : ℕ) (Λ : ℝ) :
    ∃ N : ℕ,
      ∀ (ι : Type u) (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N := by
  refine ⟨⌊(N0 : ℝ) * (2 * κ * Λ ^ 2) ^ n⌋₊, ?_⟩
  intro ι c s hs hN0 hΛ x T hT
  exact Nat.le_floor (cube_enlarged_overlap_card_le hκ hs hN0 hΛ x T hT)

/-- Volume count: the cube `j` has at most `N0 * ((2 * Λ + 1) * κ * Λ) ^ n`
neighbours. The paper's proof squares sums over neighbours, which needs this. -/
theorem cubeNeighbors_card_le {ι : Type*} [Fintype ι] {κ : ℝ} (hκ : 1 < κ) {c : ι → E}
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {N0 : ℕ}
    (hN0 : ∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0)
    {Λ : ℝ} (hΛ : ∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) (j : ι) :
    ((cubeNeighbors κ c s j).card : ℝ) ≤ N0 * ((2 * Λ + 1) * κ * Λ) ^ n := by
  have hκ0 : 0 < κ := by linarith
  have hsj : 0 < s j := hs j
  have hΛ1 : 1 ≤ Λ := by
    have h := hΛ j j (cubeNeighbor_refl hκ0.le hsj.le)
    exact le_of_mul_le_mul_right (by linarith) hsj
  have hΛ0 : 0 < Λ := by linarith
  have hup : ∀ i ∈ cubeNeighbors κ c s j, s i ≤ Λ * s j :=
    fun i hi => hΛ i j (cubeNeighbors_mem_iff.mp hi)
  have hlo : ∀ i ∈ cubeNeighbors κ c s j, s j ≤ Λ * s i :=
    fun i hi => hΛ j i (cubeNeighbor_symm (cubeNeighbors_mem_iff.mp hi))
  have hsub : ∀ i ∈ cubeNeighbors κ c s j,
      cube (c i) (s i) ⊆ cube (c j) ((2 * Λ + 1) * κ * s j) := by
    intro i hi y hy k
    obtain ⟨z, hzi, hzj⟩ := cubeNeighbors_mem_iff.mp hi
    have h1 : |y k - c i k| ≤ s i / 2 := hy k
    have h2 : |z k - c i k| ≤ κ * s i / 2 := hzi k
    have h3 : |z k - c j k| ≤ κ * s j / 2 := hzj k
    have h5 : κ * s i ≤ κ * (Λ * s j) := mul_le_mul_of_nonneg_left (hup i hi) hκ0.le
    have hb : s i / 2 + κ * s i / 2 + κ * s j / 2 ≤ (2 * Λ + 1) * κ * s j / 2 := by
      nlinarith [hs i, mul_pos hκ0 (hs i)]
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hbig : 0 ≤ (2 * Λ + 1) * κ * s j := by positivity
  have h7 := cube_card_mul_pow_le (cubeNeighbors κ c s j) c s N0 hN0 (c j) hbig hsub
    (σ := s j / Λ) (by positivity)
    (fun i hi => by
      rw [div_le_iff₀ hΛ0]
      linarith [hlo i hi])
  have h8 : ((2 * Λ + 1) * κ * s j) ^ n = ((2 * Λ + 1) * κ * Λ) ^ n * (s j / Λ) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h8, ← mul_assoc] at h7
  exact le_of_mul_le_mul_right h7 (by positivity)

/-- **Bounded number of neighbours**, with the bound chosen before the family. -/
theorem cubeNeighbors_exists_card_bound (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 : ℕ) (Λ : ℝ) :
    ∃ M : ℕ,
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        ∀ j, (cubeNeighbors κ c s j).card ≤ M := by
  refine ⟨⌊(N0 : ℝ) * ((2 * Λ + 1) * κ * Λ) ^ n⌋₊, ?_⟩
  intro ι _ c s hs hN0 hΛ j
  exact Nat.le_floor (cubeNeighbors_card_le hκ hs hN0 hΛ j)

/-! ## Bundled statements for the gluing lemma -/

/-- **Structure of the partition** (no constants). For a finite family of
cubes with positive sides and `κ > 1`: the domain is open and contains every
cube; the members are smooth on it, take values in `[0, 1]`, sum to one on
it, and vanish off their enlarged cubes; combinations of constants are smooth
on the domain, hence `C¹` on any set inside the union of the cubes; and the
two pointwise comparisons used in the paper hold on each cube. -/
theorem cubePartition_structure {ι : Type*} [Fintype ι] {κ : ℝ} (hκ : 1 < κ)
    (c : ι → E) (s : ι → ℝ) (hs : ∀ i, 0 < s i) :
    IsOpen (cubePartitionDomain κ c s) ∧
    (⋃ j, cube (c j) (s j)) ⊆ cubePartitionDomain κ c s ∧
    cubePartitionDomain κ c s ⊆ ⋃ j, cube (c j) (κ * s j) ∧
    (∀ j, ∀ x ∈ cubePartitionDomain κ c s, ContDiffAt ℝ ∞ (cubePartitionFun κ c s j) x) ∧
    (∀ j x, 0 ≤ cubePartitionFun κ c s j x ∧ cubePartitionFun κ c s j x ≤ 1) ∧
    (∀ x ∈ cubePartitionDomain κ c s, ∑ j, cubePartitionFun κ c s j x = 1) ∧
    (∀ j x, x ∉ cube (c j) (κ * s j) → cubePartitionFun κ c s j x = 0) ∧
    (∀ (a : ι → ℝ), ∀ x ∈ cubePartitionDomain κ c s,
      ContDiffAt ℝ ∞ (cubePartitionCombination κ c s a) x) ∧
    (∀ (a : ι → ℝ) (F : Set E), F ⊆ ⋃ j, cube (c j) (s j) →
      ContDiffOn ℝ 1 (cubePartitionCombination κ c s a) F) ∧
    (∀ (a : ι → ℝ) (t : ℝ) (j : ι) (x : E), x ∈ cube (c j) (s j) →
      |t - cubePartitionCombination κ c s a x| ≤
        ∑ i ∈ cubeNeighbors κ c s j, cubePartitionFun κ c s i x * |t - a i|) ∧
    (∀ (a : ι → ℝ) (j : ι) (x : E), x ∈ cube (c j) (s j) →
      |cubePartitionCombination κ c s a x - a j| ≤
        ∑ i ∈ cubeNeighbors κ c s j, |a i - a j|) :=
  ⟨cubePartitionDomain_isOpen,
    iUnion_subset fun j => cubePartitionDomain_cube_subset hκ hs j,
    cubePartitionDomain_subset hκ hs,
    fun j _ hx => cubePartitionFun_contDiffAt j hx,
    fun j x => ⟨cubePartitionFun_nonneg j x, cubePartitionFun_le_one j x⟩,
    fun _ hx => cubePartitionFun_sum_eq_one hx,
    fun j _ hx => cubePartitionFun_eq_zero hκ (hs j) hx,
    fun a _ hx => cubePartitionCombination_contDiffAt a hx,
    fun a _ hF => cubePartitionCombination_contDiffOn_one hκ hs a hF,
    fun a t _ _ hx => cubePartitionCombination_sub_le_weighted hκ hs a t hx,
    fun a _ _ hx => cubePartitionCombination_sub_le hκ hs a hx⟩

/-- **Gradient bounds of the partition**, with the constants chosen before
the family of cubes. Hypotheses: every point lies in at most `N` of the
ENLARGED cubes, and neighbouring cubes have sides within the factor `Λ`.
`K1` and `K2` depend only on the dimension, `κ`, `N` and `Λ`. -/
theorem cubePartition_gradient_bounds (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N : ℕ) (Λ : ℝ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (κ * s i)) → T.card ≤ N) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤ K1 / s j) ∧
        (∀ (a : ι → ℝ) j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionCombination κ c s a) x‖ ^ 2 ≤
            K2 / s j ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2) := by
  obtain ⟨K1, hK1, h1⟩ := cubePartitionFun_exists_fderiv_bound.{u} n hκ N Λ
  obtain ⟨K2, hK2, h2⟩ := cubePartitionCombination_exists_fderiv_bound.{u} n hκ N Λ
  exact ⟨K1, K2, hK1, hK2, fun ι _ c s hs hN hΛ =>
    ⟨h1 ι c s hs hN hΛ, h2 ι c s hs hN hΛ⟩⟩

/-- **Gradient bounds under the paper's hypotheses**: bounded overlap of the
cubes themselves (at most `N0` at any point) and sides of neighbours within
the factor `Λ`. `K1` and `K2` depend only on the dimension, `κ`, `N0`, `Λ`. -/
theorem cubePartition_gradient_bounds_of_cube_overlap (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 : ℕ)
    (Λ : ℝ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        (∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
        (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
        (∀ i j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionFun κ c s i) x‖ ≤ K1 / s j) ∧
        (∀ (a : ι → ℝ) j x, x ∈ cube (c j) (s j) →
          ‖fderiv ℝ (cubePartitionCombination κ c s a) x‖ ^ 2 ≤
            K2 / s j ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2) := by
  obtain ⟨N, hN⟩ := cube_enlarged_overlap_of_overlap.{u} n hκ N0 Λ
  obtain ⟨K1, K2, hK1, hK2, h⟩ := cubePartition_gradient_bounds.{u} n hκ N Λ
  exact ⟨K1, K2, hK1, hK2, fun ι _ c s hs hN0 hΛ =>
    h ι c s hs (hN ι c s hs hN0 hΛ) hΛ⟩

/-- **The partition of unity the gluing lemma takes for granted**, stated
without reference to how it is built. The constants come first; then, for
every finite family of cubes with positive sides, there are functions `ψ` and
an open set `V` containing every cube, with all the properties used in the
paper's proof. The two gradient bounds hold under bounded overlap of the
cubes and comparable sides of neighbours. -/
theorem cube_exists_partition_of_unity (n : ℕ) {κ : ℝ} (hκ : 1 < κ) (N0 : ℕ) (Λ : ℝ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ (ι : Type u) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (s : ι → ℝ),
        (∀ i, 0 < s i) →
        ∃ (ψ : ι → EuclideanSpace ℝ (Fin n) → ℝ) (V : Set (EuclideanSpace ℝ (Fin n))),
          IsOpen V ∧
          (⋃ j, cube (c j) (s j)) ⊆ V ∧
          (∀ j, ∀ x ∈ V, ContDiffAt ℝ ∞ (ψ j) x) ∧
          (∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1) ∧
          (∀ x ∈ V, ∑ j, ψ j x = 1) ∧
          (∀ j x, x ∉ cube (c j) (κ * s j) → ψ j x = 0) ∧
          (∀ (a : ι → ℝ), ∀ x ∈ V, ContDiffAt ℝ ∞ (fun y => ∑ i, a i * ψ i y) x) ∧
          (∀ (a : ι → ℝ) (F : Set (EuclideanSpace ℝ (Fin n))), F ⊆ ⋃ j, cube (c j) (s j) →
            ContDiffOn ℝ 1 (fun y => ∑ i, a i * ψ i y) F) ∧
          (∀ (a : ι → ℝ) (t : ℝ) (j : ι) (x : EuclideanSpace ℝ (Fin n)),
            x ∈ cube (c j) (s j) →
            |t - ∑ i, a i * ψ i x| ≤ ∑ i ∈ cubeNeighbors κ c s j, ψ i x * |t - a i|) ∧
          (∀ (a : ι → ℝ) (j : ι) (x : EuclideanSpace ℝ (Fin n)),
            x ∈ cube (c j) (s j) →
            |∑ i, a i * ψ i x - a j| ≤ ∑ i ∈ cubeNeighbors κ c s j, |a i - a j|) ∧
          ((∀ x, ∀ T : Finset ι, (∀ i ∈ T, x ∈ cube (c i) (s i)) → T.card ≤ N0) →
            (∀ i j, cubeNeighbor κ c s i j → s i ≤ Λ * s j) →
            (∀ i j x, x ∈ cube (c j) (s j) → ‖fderiv ℝ (ψ i) x‖ ≤ K1 / s j) ∧
            (∀ (a : ι → ℝ) j x, x ∈ cube (c j) (s j) →
              ‖fderiv ℝ (fun y => ∑ i, a i * ψ i y) x‖ ^ 2 ≤
                K2 / s j ^ 2 * ∑ i ∈ cubeNeighbors κ c s j, (a i - a j) ^ 2)) := by
  obtain ⟨K1, K2, hK1, hK2, h⟩ := cubePartition_gradient_bounds_of_cube_overlap.{u} n hκ N0 Λ
  refine ⟨K1, K2, hK1, hK2, fun ι _ c s hs => ?_⟩
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10, h11⟩ := cubePartition_structure hκ c s hs
  exact ⟨cubePartitionFun κ c s, cubePartitionDomain κ c s, h1, h2, h4, h5, h6, h7, h8, h9,
    h10, h11, fun hN0 hΛ => h ι c s hs hN0 hΛ⟩

end BrownRadial
