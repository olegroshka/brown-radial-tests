import Gaussian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric
open scoped NNReal
namespace BrownRadial

noncomputable def logValleyProfile (p : ℝ × ℝ) : ℝ :=
  Real.log (1+p.2^2) - Real.log (1+p.1+p.2^2)

noncomputable def logValleyDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (2*p.2/(1+p.2^2)-2*p.2/(1+p.1+p.2^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
    (1/(1+p.1+p.2^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ

theorem logValley_hasFDerivAt {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    HasFDerivAt logValleyProfile (logValleyDerivative p) p := by
  have hA : (1+p.2^2) ≠ 0 := ne_of_gt (by positivity)
  have hB : (1+p.1+p.2^2) ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg p.2])
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have h := ((hasFDerivAt_const (1 : ℝ) p).add (hs.pow 2)).log hA
  have h' := (((hasFDerivAt_const (1 : ℝ) p).add hf).add (hs.pow 2)).log hB
  apply (h.sub h').congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [logValleyDerivative, div_eq_mul_inv]
  ring

/-- The sum of the absolute coordinate derivatives is at most one on the
nonnegative quadrant. This proves the sharp logarithmic bound without taking
derivatives of the distance function on its singular set. -/
theorem logValleyDerivative_norm_le {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    ‖logValleyDerivative p‖ ≤ 1 := by
  let A := 1+p.2^2
  let B := 1+p.1+p.2^2
  let a := 2*p.2/A - 2*p.2/B
  let b := 1/B
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; nlinarith [sq_nonneg p.2]
  have ha : 0 ≤ a := sub_nonneg.mpr (div_le_div_of_nonneg_left
    (by nlinarith [hp.2]) hA (by dsimp [A, B]; linarith [hp.1]))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : a+b = (2*p.2*p.1+A)/(A*B) := by
    dsimp [a, b]
    field_simp [hA.ne', hB.ne']
    dsimp [A, B]
    ring
  have hab : a+b ≤ 1 := by
    rw [he, div_le_one (mul_pos hA hB)]
    have hprod := mul_nonneg hp.1 (sq_nonneg (p.2-1))
    have hsq := mul_nonneg (sq_nonneg p.2) hA.le
    dsimp [A, B] at *
    nlinarith
  change ‖a • ContinuousLinearMap.snd ℝ ℝ ℝ - b • ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1
  calc
    _ ≤ ‖a • ContinuousLinearMap.snd ℝ ℝ ℝ‖ + ‖b • ContinuousLinearMap.fst ℝ ℝ ℝ‖ := norm_sub_le _ _
    _ = a+b := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ 1 := hab

theorem logValleyProfile_lipschitz :
    LipschitzOnWith 1 logValleyProfile ((Ici (0 : ℝ)) ×ˢ (Ici (0 : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := logValleyDerivative)
  · intro p hp
    exact (logValley_hasFDerivAt hp).hasFDerivWithinAt
  · intro p hp
    exact_mod_cast logValleyDerivative_norm_le hp
  · exact (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))

variable {E : Type*} [NormedAddCommGroup E]

/-- The log profile in the lattice construction is globally 1-Lipschitz for
the distance to any set, including on the medial surfaces. -/
theorem lattice_log_profile_lipschitz (Γ : Set E) :
    LipschitzWith 1 (fun x => logValleyProfile (‖x‖, infDist x Γ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := logValleyProfile_lipschitz.dist_le_mul (‖x‖, infDist x Γ)
    (show (‖x‖, infDist x Γ) ∈ (Ici (0 : ℝ)) ×ˢ (Ici (0 : ℝ)) from
      ⟨norm_nonneg _, infDist_nonneg⟩)
    (‖y‖, infDist y Γ)
    (show (‖y‖, infDist y Γ) ∈ (Ici (0 : ℝ)) ×ˢ (Ici (0 : ℝ)) from
      ⟨norm_nonneg _, infDist_nonneg⟩)
  simp only [NNReal.coe_one, one_mul] at h ⊢
  apply h.trans
  rw [Prod.dist_eq, max_le_iff]
  exact ⟨by simpa only [dist_eq_norm] using dist_norm_norm_le x y,
    by simpa using (lipschitz_infDist_pt Γ).dist_le_mul x y⟩

/-- The weight of equation (w), for an arbitrary set of valleys. -/
noncomputable def latticeWeight (Γ : Set E) (α : ℝ) (x : E) : ℝ :=
  ((1+(infDist x Γ)^2)/(1+‖x‖+(infDist x Γ)^2)) ^ (α/2)

theorem latticeWeight_pos (Γ : Set E) (α : ℝ) (x : E) : 0 < latticeWeight Γ α x := by
  apply Real.rpow_pos_of_pos
  exact div_pos (by positivity) (by positivity)

theorem latticeWeight_log (Γ : Set E) (α : ℝ) (x : E) :
    Real.log (latticeWeight Γ α x) = (α/2) * logValleyProfile (‖x‖, infDist x Γ) := by
  have hA : 0 < 1+(infDist x Γ)^2 := by positivity
  have hB : 0 < 1+‖x‖+(infDist x Γ)^2 := by positivity
  rw [latticeWeight, Real.log_rpow (div_pos hA hB), Real.log_div hA.ne' hB.ne']
  rfl

/-- The paper's exact alpha/2 logarithmic Lipschitz bound, globally and with
no smoothness assumption on the valley set. -/
theorem latticeWeight_log_lipschitz (Γ : Set E) (α : ℝ≥0) :
    LipschitzWith (α/2) (fun x => Real.log (latticeWeight Γ (α : ℝ) x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (lattice_log_profile_lipschitz Γ).dist_le_mul x y
  have ha : 0 ≤ (α : ℝ)/2 := by positivity
  simpa only [latticeWeight_log, Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_nonneg ha, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one, one_mul]
    using mul_le_mul_of_nonneg_left h ha

end BrownRadial
