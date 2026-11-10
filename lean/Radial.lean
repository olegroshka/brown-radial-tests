import Analytic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
namespace BrownRadial

def dyadicAnnulus (j : ℕ) : Set ℝ := Ico ((2 : ℝ)^j) ((2 : ℝ)^(j+1))

theorem dyadicAnnulus_cover : (⋃ j, dyadicAnnulus j) = Ici 1 := by
  ext x
  simp only [mem_iUnion, dyadicAnnulus, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨j, hj, _⟩
    exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hj
  · intro hx
    exact exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)

theorem dyadicAnnulus_disjoint : Pairwise (fun i j => Disjoint (dyadicAnnulus i) (dyadicAnnulus j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · apply Ico_disjoint_Ico.mpr
    exact (min_le_left _ _).trans ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.succ_le_of_lt h)).trans (le_max_right _ _))
  · apply Ico_disjoint_Ico.mpr
    exact (min_le_right _ _).trans ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.succ_le_of_lt h)).trans (le_max_left _ _))

theorem summable_dyadic_of_integrable {f : ℝ → ℝ}
    (h : IntegrableOn f (Ici 1)) :
    Summable (fun j => ∫ x in dyadicAnnulus j, f x) := by
  have hU : IntegrableOn f (⋃ j, dyadicAnnulus j) := by
    rw [dyadicAnnulus_cover]
    exact h
  exact (hasSum_integral_iUnion (fun _ => measurableSet_Ico)
    dyadicAnnulus_disjoint hU).summable

/-- Exact equivalence between convergence on the half-line and summability of
dyadic integrals, for a nonnegative function integrable on each annulus. -/
theorem integrableOn_halfline_iff_dyadic {f : ℝ → ℝ}
    (hn : ∀ x, 0 ≤ f x)
    (hi : ∀ j, IntegrableOn f (dyadicAnnulus j)) :
    IntegrableOn f (Ici 1) ↔ Summable (fun j => ∫ x in dyadicAnnulus j, f x) := by
  constructor
  · intro h
    rw [← dyadicAnnulus_cover] at h
    exact (hasSum_integral_iUnion (fun _ => measurableSet_Ico)
      dyadicAnnulus_disjoint h).summable
  · intro h
    rw [← dyadicAnnulus_cover]
    apply integrableOn_iUnion_of_summable_integral_norm hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using h

/-- Fully connected analytic implication underlying `cor:cs` for locally
integrable positive radial area and continuous volume profiles. Shell mass domination is
explicit here; the next theorem instantiates it for an actual primitive. -/
theorem radial_integrability_implication {a V : ℝ → ℝ}
    (ha : ∀ l u, IntervalIntegrable a volume l u) (hapos : ∀ x, 0 < x → 0 < a x)
    (hV : Continuous V) (hVpos : ∀ r, 0 < r → 0 < V r)
    (hVmono : MonotoneOn V (Ici 0))
    (hmass : ∀ R, 0 < R → (∫ x in Icc R (2*R), a x) ≤ V (2*R))
    (hsphere : IntegrableOn (fun r => 1 / a r) (Ici 1)) :
    IntegrableOn (fun r => r / V r) (Ici 1) := by
  let v : ℕ → ℝ := fun j => ∫ r in dyadicAnnulus j, r / V r
  let s : ℕ → ℝ := fun j => ∫ r in dyadicAnnulus j, 1 / a r
  have hpow (j : ℕ) : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hvInt (j : ℕ) : IntegrableOn (fun r => r / V r) (Icc ((2 : ℝ)^j) (2^(j+1))) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.div hV.continuousOn
    intro r hr
    exact ne_of_gt (hVpos r (lt_of_lt_of_le (by positivity) hr.1))
  have hvNonneg (j : ℕ) : 0 ≤ v j := by
    apply setIntegral_nonneg measurableSet_Ico
    intro r hr
    exact le_of_lt (div_pos (lt_of_lt_of_le (by positivity) hr.1)
      (hVpos r (lt_of_lt_of_le (by positivity) hr.1)))
  have hsSum : Summable s := summable_dyadic_of_integrable hsphere
  have upper (j : ℕ) : v j ≤ 2 * ((4 : ℝ)^j / V (2^j)) := by
    have h := volume_annulus_upper (V := V) (R := (2 : ℝ)^j)
      (by positivity) (hVpos _ (by positivity))
      (fun r hr => hVmono (show 0 ≤ (2 : ℝ)^j by positivity)
        (show 0 ≤ r from (show 0 ≤ (2 : ℝ)^j by positivity).trans hr.1) hr.1)
      (by simpa [pow_succ, mul_comm] using hvInt j)
    dsimp [v, dyadicAnnulus]
    rw [← integral_Icc_eq_integral_Ico]
    simpa [pow_succ, hpow, mul_comm, mul_div_assoc] using h
  have lower (j : ℕ) : (4 : ℝ)^j / V (2^(j+1)) ≤ s j := by
    have hR : (0 : ℝ) < 2^j := by positivity
    have hpos : 0 < ∫ x in Icc ((2 : ℝ)^j) (2*2^j), a x := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (2 : ℝ)^j ≤ 2*2^j)]
      exact intervalIntegral.intervalIntegral_pos_of_pos_on (ha _ _)
        (fun x hx => hapos x (hR.trans hx.1)) (by linarith)
    have harea : IntegrableOn a (Icc ((2 : ℝ)^j) (2*2^j)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (f := a)
        (by linarith : (2 : ℝ)^j ≤ 2*2^j)).mp (ha ((2 : ℝ)^j) (2*2^j))
    have hinv : IntegrableOn (fun r => 1/a r) (Icc ((2 : ℝ)^j) (2*2^j)) :=
      hsphere.mono_set (fun x hx => (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx.1)
    have h := sphere_annulus_lower (R := (2 : ℝ)^j) (U := V (2*2^j))
      (by positivity) (hVpos _ (by positivity)) (fun x hx => hapos x (hR.trans_le hx.1)) harea
      hinv hpos (hmass _ (by positivity))
    dsimp [s, dyadicAnnulus]
    rw [← integral_Icc_eq_integral_Ico]
    simpa [pow_succ, hpow, mul_comm] using h
  have hvSum : Summable v := by
    by_contra h
    exact sphere_series_diverges (fun j => V (2^j)) v s
      (fun j => hVpos _ (by positivity)) hvNonneg upper lower h hsSum
  rw [← dyadicAnnulus_cover]
  apply integrableOn_iUnion_of_summable_integral_norm
    (fun j => (hvInt j).mono_set Ico_subset_Icc_self)
  convert hvSum using 1
  funext j
  apply setIntegral_congr_fun measurableSet_Ico
  intro r hr
  dsimp only
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (lt_of_lt_of_le (by positivity) hr.1)
    (hVpos r (lt_of_lt_of_le (by positivity) hr.1)))]

/-- Cumulative volume associated with a one-dimensional area profile. -/
noncomputable def cumulativeArea (a : ℝ → ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, a x

/-- The complete locally integrable-area version of the sphere/volume implication:
if the sphere resistance is integrable, then so is the volume resistance.
All annulus bounds, the dyadic cover, and the infinite sum passage are proved. -/
theorem locally_integrable_area_volume_integrable {a : ℝ → ℝ}
    (ha : ∀ l u, IntervalIntegrable a volume l u) (hapos : ∀ x, 0 < x → 0 < a x)
    (hsphere : IntegrableOn (fun r => 1 / a r) (Ici 1)) :
    IntegrableOn (fun r => r / cumulativeArea a r) (Ici 1) := by
  apply radial_integrability_implication ha hapos
    (intervalIntegral.continuous_primitive ha 0)
    ?_ ?_ ?_ hsphere
  · intro r hr
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (ha _ _)
      (fun x hx => hapos x hx.1) hr
  · intro r hr s hs hrs
    exact intervalIntegral.integral_mono_interval le_rfl hr hrs
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
        (fun x hx => (hapos x hx.1).le))) (ha _ _)
  · intro R hR
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : R ≤ 2*R)]
    exact intervalIntegral.integral_mono_interval hR.le (by linarith) le_rfl
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
        (fun x hx => (hapos x hx.1).le))) (ha _ _)

theorem continuous_area_volume_integrable {a : ℝ → ℝ}
    (ha : Continuous a) (hapos : ∀ x, 0 < x → 0 < a x)
    (hsphere : IntegrableOn (fun r => 1 / a r) (Ici 1)) :
    IntegrableOn (fun r => r / cumulativeArea a r) (Ici 1) :=
  locally_integrable_area_volume_integrable (fun _ _ => ha.intervalIntegrable _ _) hapos hsphere

/-- Sphere-test domination in the locally integrable area-profile formulation. -/
theorem sphere_test_dominates_volume_test {a : ℝ → ℝ}
    (ha : ∀ l u, IntervalIntegrable a volume l u) (hapos : ∀ x, 0 < x → 0 < a x)
    (hvolume : ¬ IntegrableOn (fun r => r / cumulativeArea a r) (Ici 1)) :
    ¬ IntegrableOn (fun r => 1 / a r) (Ici 1) :=
  fun h => hvolume (locally_integrable_area_volume_integrable ha hapos h)

/-- Divergence formulation of the same continuous-area result. -/
theorem continuous_area_volume_diverges {a : ℝ → ℝ}
    (ha : Continuous a) (hapos : ∀ x, 0 < x → 0 < a x)
    (hvolume : ¬ IntegrableOn (fun r => r / cumulativeArea a r) (Ici 1)) :
    ¬ IntegrableOn (fun r => 1 / a r) (Ici 1) := by
  exact fun h => hvolume (continuous_area_volume_integrable ha hapos h)

end BrownRadial
