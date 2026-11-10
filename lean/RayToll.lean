import LatticeGeometry
import SphericalA2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Ray part of `thm:B`(b) for the actual lattice weight of equation (w).

For every unit direction and every shell `k ≥ 4` the ray passes within
distance `sqrt (1 + pi^2/16)` of an actual lattice circle on a radial interval
of length two; there the weight is at most `(2.62/R)^(alpha/2)`, as in the
paper. For `alpha ≥ 4` this gives a toll of at least `1/4` per shell, so every
ray integral diverges and the analytic hypothesis of Brown's ray test fails,
both for the weight and for its Gaussian marginal.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal
namespace BrownRadial

/-- A unit planar direction aligned with a given planar vector. When the
vector vanishes (a ray along the polar axis) every direction is aligned. -/
theorem exists_planar_direction (a b : ℝ) :
    ∃ c s : ℝ, c^2 + s^2 = 1 ∧ a*c + b*s = Real.sqrt (a^2+b^2) := by
  by_cases h : a^2 + b^2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact ⟨1, 0, by norm_num, by simp [ha, hb]⟩
  · have hpos : 0 < a^2+b^2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hs : 0 < Real.sqrt (a^2+b^2) := Real.sqrt_pos.mpr hpos
    have hsq : Real.sqrt (a^2+b^2) ^ 2 = a^2+b^2 := Real.sq_sqrt hpos.le
    refine ⟨a / Real.sqrt (a^2+b^2), b / Real.sqrt (a^2+b^2), ?_, ?_⟩
    · rw [div_pow, div_pow, ← add_div, hsq, div_self h]
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hs.ne']
      nlinarith [hsq]

/-- The point of polar angle `θ` on the sphere of radius `R` in the meridian
half-plane with unit planar direction `(c,s)`. -/
noncomputable def meridianPoint (R θ c s : ℝ) : LatticeSpace :=
  WithLp.toLp 2 ![R*Real.sin θ*c, R*Real.sin θ*s, R*Real.cos θ]

theorem meridianPoint_apply_zero (R θ c s : ℝ) :
    meridianPoint R θ c s 0 = R*Real.sin θ*c := by simp [meridianPoint]

theorem meridianPoint_apply_one (R θ c s : ℝ) :
    meridianPoint R θ c s 1 = R*Real.sin θ*s := by simp [meridianPoint]

theorem meridianPoint_apply_two (R θ c s : ℝ) :
    meridianPoint R θ c s 2 = R*Real.cos θ := by simp [meridianPoint]

theorem meridianPoint_mem {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) {c s : ℝ} (hcs : c^2+s^2 = 1) :
    meridianPoint R θ c s ∈ latitudeCircle R θ := by
  refine ⟨?_, meridianPoint_apply_two R θ c s⟩
  apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, meridianPoint_apply_zero,
    meridianPoint_apply_one, meridianPoint_apply_two]
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination R^2*(Real.sin θ)^2*hcs + R^2*Real.sin_sq_add_cos_sq θ

theorem unit_vector_coordinates (u : LatticeSpace) (hu : ‖u‖ = 1) :
    (u 0)^2 + (u 1)^2 + (u 2)^2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq u
  rw [hu, Fin.sum_univ_three] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  linarith

/-- Exact squared distance from a point of the ray to the aligned point of a
latitude circle: radial offset plus the chord term in the polar angle. -/
theorem ray_meridian_dist_sq (u : LatticeSpace) (hu : ‖u‖ = 1) (r R θ : ℝ) {c s : ℝ}
    (hcs : c^2+s^2 = 1) (halign : u 0*c + u 1*s = Real.sqrt ((u 0)^2+(u 1)^2)) :
    dist (r • u) (meridianPoint R θ c s)^2 =
      (r-R)^2 + 2*r*R*(1 - Real.cos (Real.arccos (u 2) - θ)) := by
  have hc := unit_vector_coordinates u hu
  have h2 : (u 2)^2 ≤ 1 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have habs := abs_le_one_iff_mul_self_le_one.mpr (by nlinarith : u 2 * u 2 ≤ 1)
  have hcos : Real.cos (Real.arccos (u 2)) = u 2 :=
    Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2
  have hsin : Real.sin (Real.arccos (u 2)) = Real.sqrt ((u 0)^2+(u 1)^2) := by
    rw [Real.sin_arccos]
    congr 1
    linarith
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three, meridianPoint_apply_zero,
    meridianPoint_apply_one, meridianPoint_apply_two, Real.cos_sub, hcos, hsin]
  simp only [Real.dist_eq, sq_abs, PiLp.smul_apply, smul_eq_mul]
  linear_combination r^2*hc + R^2*(Real.sin θ)^2*hcs + R^2*Real.sin_sq_add_cos_sq θ
    - 2*r*R*Real.sin θ*halign

/-- In every shell `k ≥ 4` the ray in direction `u` stays, on a radial interval
of length two around an actual circle radius `R`, within squared distance
`1 + pi^2/16` of the lattice. This is the paper's bound, on its interval. -/
theorem lattice_ray_near_circle (u : LatticeSpace) (hu : ‖u‖ = 1) {k : ℕ} (hk : 4 ≤ k) :
    ∃ R : ℝ, (2:ℝ)^k ≤ R ∧ R + 4 ≤ (2:ℝ)^(k+1) ∧
      ∀ r ∈ Icc (R-1) (R+1), (infDist (r • u) latticeValleys)^2 ≤ 1 + Real.pi^2/16 := by
  obtain ⟨i, j, hθ⟩ := lattice_polar_coverage k (Real.arccos_nonneg (u 2)) (Real.arccos_le_pi (u 2))
  obtain ⟨c, s, hcs, halign⟩ := exists_planar_direction (u 0) (u 1)
  have hR := latticeCircleRadius_bounds k i
  have hgap := latticeCircleRadius_upper_gap k i
  rw [lattice_radial_mesh] at hgap
  have h4 : (4:ℝ) ≤ (2:ℝ)^(k/2) := by
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (2:ℝ)^(k/2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h16 : (16:ℝ) ≤ (2:ℝ)^k := by
    calc (16:ℝ) = (2:ℝ)^4 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hR0 : 0 ≤ latticeCircleRadius k i := by linarith
  refine ⟨latticeCircleRadius k i, hR.1, by linarith, ?_⟩
  intro r hr
  have hmem : meridianPoint (latticeCircleRadius k i)
      (latticePolarAngle k (latticeAngleIndex k (i,j))) c s ∈ latticeValleys :=
    mem_iUnion.mpr ⟨⟨k, hk⟩, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, meridianPoint_mem hR0 _ hcs⟩⟩⟩
  have hd := infDist_le_dist_of_mem (x := r • u) hmem
  have hsq := pow_le_pow_left₀ infDist_nonneg hd 2
  rw [ray_meridian_dist_sq u hu r _ _ hcs halign] at hsq
  set R := latticeCircleRadius k i
  set δ := Real.arccos (u 2) - latticePolarAngle k (latticeAngleIndex k (i,j))
  have hP : (0:ℝ) < (2:ℝ)^(k+1) := by positivity
  have hN : (latticeCircleCount k : ℝ) = 2 * (2:ℝ)^(k+1) := by
    unfold latticeCircleCount
    push_cast
    ring
  have hδ : |δ| ≤ Real.pi / (4 * (2:ℝ)^(k+1)) := by
    have h := hθ
    rw [hN] at h
    convert h using 2
    ring
  have hPδ : (2:ℝ)^(k+1) * |δ| ≤ Real.pi/4 := by
    have h := mul_le_mul_of_nonneg_left hδ hP.le
    have he : (2:ℝ)^(k+1) * (Real.pi / (4 * (2:ℝ)^(k+1))) = Real.pi/4 := by field_simp
    rwa [he] at h
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hrP : r ≤ (2:ℝ)^(k+1) := by linarith [hr.2]
  have hRP : R ≤ (2:ℝ)^(k+1) := by linarith
  have h1 : r * |δ| ≤ Real.pi/4 := (mul_le_mul_of_nonneg_right hrP (abs_nonneg δ)).trans hPδ
  have h2 : R * |δ| ≤ Real.pi/4 := (mul_le_mul_of_nonneg_right hRP (abs_nonneg δ)).trans hPδ
  have hprod : (r * |δ|) * (R * |δ|) ≤ (Real.pi/4) * (Real.pi/4) :=
    mul_le_mul h1 h2 (mul_nonneg hR0 (abs_nonneg δ)) (by positivity)
  have hcos : 1 - Real.cos δ ≤ δ^2/2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  have hchord : 2*r*R*(1 - Real.cos δ) ≤ r*R*δ^2 := by
    have h := mul_le_mul_of_nonneg_left hcos (by positivity : 0 ≤ 2*r*R)
    linarith
  have habs : |δ| * |δ| = δ^2 := by rw [abs_mul_abs_self, sq]
  have hradial : (r-R)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)]
  have hrew : r*R*δ^2 = (r * |δ|) * (R * |δ|) := by rw [← habs]; ring
  have hpi : (Real.pi/4) * (Real.pi/4) = Real.pi^2/16 := by ring
  linarith

/-- The paper's weight bound on the toll interval, for every exponent. -/
theorem lattice_ray_weight_bound {α : ℝ} (hα : 0 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1)
    {k : ℕ} (hk : 4 ≤ k) :
    ∃ R : ℝ, (2:ℝ)^k ≤ R ∧ R + 4 ≤ (2:ℝ)^(k+1) ∧
      ∀ r ∈ Icc (R-1) (R+1),
        latticeWeight latticeValleys α (r • u) ≤ ((2.62:ℝ)/R)^(α/2) := by
  obtain ⟨R, hRlo, hRhi, hnear⟩ := lattice_ray_near_circle u hu hk
  have h16 : (16:ℝ) ≤ (2:ℝ)^k := by
    calc (16:ℝ) = (2:ℝ)^4 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hR : 0 < R := by linarith
  refine ⟨R, hRlo, hRhi, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hd := hnear r hr
  have hpi : Real.pi^2/16 ≤ 0.62 := by
    have hp2 : Real.pi^2 ≤ (3.1416:ℝ)^2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
    norm_num at hp2 ⊢
    linarith
  have hnorm : ‖r • u‖ = r := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  unfold latticeWeight
  rw [hnorm]
  set d := infDist (r • u) latticeValleys
  have hd0 : 0 ≤ d^2 := sq_nonneg d
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  apply (div_le_div_iff₀ (by positivity) hR).mpr
  nlinarith [mul_nonneg hd0 hR.le, hr.1]

/-- For `alpha ≥ 4` the ray integrand is at least `1/8` on the toll interval. -/
theorem lattice_ray_toll_pointwise {α : ℝ} (hα : 4 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1)
    {k : ℕ} (hk : 4 ≤ k) :
    ∃ R : ℝ, (2:ℝ)^k ≤ R ∧ R + 4 ≤ (2:ℝ)^(k+1) ∧
      ∀ r ∈ Icc (R-1) (R+1),
        (1/8 : ℝ) ≤ 1 / (r^2 * latticeWeight latticeValleys α (r • u)) := by
  obtain ⟨R, hRlo, hRhi, hw⟩ := lattice_ray_weight_bound (by linarith : 0 ≤ α) u hu hk
  have h16 : (16:ℝ) ≤ (2:ℝ)^k := by
    calc (16:ℝ) = (2:ℝ)^4 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hR : 0 < R := by linarith
  refine ⟨R, hRlo, hRhi, ?_⟩
  intro r hr
  have hr0 : 0 < r := by linarith [hr.1]
  have hwpos := latticeWeight_pos latticeValleys α (r • u)
  have hx0 : 0 < (2.62:ℝ)/R := by positivity
  have hx1 : (2.62:ℝ)/R ≤ 1 := by
    rw [div_le_one hR]
    linarith
  have hpow : ((2.62:ℝ)/R)^(α/2) ≤ ((2.62:ℝ)/R)^2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith : (2:ℝ) ≤ α/2)
    rwa [Real.rpow_two] at h
  have hwle : latticeWeight latticeValleys α (r • u) ≤ ((2.62:ℝ)/R)^2 := (hw r hr).trans hpow
  have hprod : r^2 * latticeWeight latticeValleys α (r • u) ≤ 8 := by
    have h1 : r^2 ≤ (R+1)^2 := pow_le_pow_left₀ hr0.le hr.2 2
    have h2 : r^2 * latticeWeight latticeValleys α (r • u) ≤ (R+1)^2 * ((2.62:ℝ)/R)^2 :=
      mul_le_mul h1 hwle hwpos.le (by positivity)
    have h3 : (R+1)^2 * ((2.62:ℝ)/R)^2 ≤ 8 := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    exact h2.trans h3
  rw [one_div, one_div]
  exact inv_anti₀ (mul_pos (by positivity) hwpos) hprod

/-- Per-shell toll with an explicit constant: for `alpha ≥ 4` the ray integral
over the (unit-shifted) dyadic shell `k ≥ 4` is at least `1/4`. -/
theorem lattice_ray_shell_toll {α : ℝ} (hα : 4 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1)
    {k : ℕ} (hk : 4 ≤ k) :
    ENNReal.ofReal (1/4) ≤ ∫⁻ r in Ico ((2:ℝ)^k - 1) ((2:ℝ)^(k+1) - 1),
      ENNReal.ofReal (1 / (r^2 * latticeWeight latticeValleys α (r • u))) := by
  obtain ⟨R, hRlo, hRhi, hpt⟩ := lattice_ray_toll_pointwise hα u hu hk
  have hsub : Icc (R-1) (R+1) ⊆ Ico ((2:ℝ)^k - 1) ((2:ℝ)^(k+1) - 1) := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  calc
    ENNReal.ofReal (1/4) = ENNReal.ofReal (1/8) * volume (Icc (R-1) (R+1)) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ = ∫⁻ _ in Icc (R-1) (R+1), ENNReal.ofReal (1/8) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Icc (R-1) (R+1),
        ENNReal.ofReal (1 / (r^2 * latticeWeight latticeValleys α (r • u))) :=
      setLIntegral_mono' measurableSet_Icc (fun r hr => ENNReal.ofReal_le_ofReal (hpt r hr))
    _ ≤ _ := lintegral_mono_set hsub

/-- Shifted dyadic shells from shell five onwards. -/
def tollShell (j : ℕ) : Set ℝ := Ico ((2:ℝ)^(j+5) - 1) ((2:ℝ)^(j+5+1) - 1)

theorem tollShell_disjoint : Pairwise (Function.onFun Disjoint tollShell) := by
  intro i j hij
  have hmono (a b : ℕ) (hab : a < b) : (2:ℝ)^(a+5+1) - 1 ≤ (2:ℝ)^(b+5) - 1 :=
    sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)) 1
  rcases lt_or_gt_of_ne hij with h | h
  · exact Ico_disjoint_Ico.mpr ((min_le_left _ _).trans ((hmono i j h).trans (le_max_right _ _)))
  · exact Ico_disjoint_Ico.mpr ((min_le_right _ _).trans ((hmono j i h).trans (le_max_left _ _)))

theorem tollShell_subset (j : ℕ) : tollShell j ⊆ Ici (16:ℝ) := by
  intro r hr
  have h32 : (32:ℝ) ≤ (2:ℝ)^(j+5) := by
    calc (32:ℝ) = (2:ℝ)^5 := by norm_num
      _ ≤ (2:ℝ)^(j+5) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h := hr.1
  simp only [mem_Ici]
  linarith

/-- Every ray pays infinitely: `thm:B`(b), ray part, for the actual lattice
weight and every unit direction. -/
theorem lattice_ray_integral_diverges {α : ℝ} (hα : 4 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1) :
    ∫⁻ r in Ici (16 : ℝ),
      ENNReal.ofReal (1 / (r ^ 2 * latticeWeight latticeValleys α (r • u))) = ⊤ := by
  apply top_le_iff.mp
  calc
    (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ENNReal.ofReal (1/4) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero
        (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 1/4)).ne').symm
    _ ≤ ∑' j : ℕ, ∫⁻ r in tollShell j,
        ENNReal.ofReal (1 / (r ^ 2 * latticeWeight latticeValleys α (r • u))) :=
      ENNReal.tsum_le_tsum (fun j => lattice_ray_shell_toll hα u hu (by omega : 4 ≤ j+5))
    _ = ∫⁻ r in ⋃ j, tollShell j,
        ENNReal.ofReal (1 / (r ^ 2 * latticeWeight latticeValleys α (r • u))) :=
      (lintegral_iUnion (fun _ => measurableSet_Ico) tollShell_disjoint _).symm
    _ ≤ _ := lintegral_mono_set (iUnion_subset tollShell_subset)

/-- If every ray integral of a positive weight on three-space diverges, the
analytic hypothesis of Brown's ray test fails: no direction has a finite ray
integral, while a set of positive measure is nonempty. -/
theorem ray_test_silent_of_divergent_rays {W : LatticeSpace → ℝ} (hW : ∀ x, 0 < W x)
    (hdiv : ∀ u : LatticeSpace, ‖u‖ = 1 →
      ∫⁻ r in Ici (16 : ℝ), ENNReal.ofReal (1 / (r ^ 2 * W (r • u))) = ⊤) :
    ¬ uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ))
        (sphereProbability (volume : Measure LatticeSpace))
        (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ LatticeSpace - 1) *
          W (r.val • θ.val))) := by
  rintro ⟨Ω, _, hpos, M, hM, hb⟩
  obtain ⟨θ, hθ⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hu : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have h := hb θ hθ
  have hcomap := lintegral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ici (a := (1:ℝ)))
    (fun r : ℝ => (ENNReal.ofReal (r ^ (Module.finrank ℝ LatticeSpace - 1) * W (r • θ.val)))⁻¹)
  rw [hcomap] at h
  apply hM
  apply top_le_iff.mp
  calc
    (⊤ : ℝ≥0∞) = ∫⁻ r in Ici (16 : ℝ), ENNReal.ofReal (1 / (r ^ 2 * W (r • θ.val))) :=
      (hdiv θ.val hu).symm
    _ ≤ ∫⁻ r in Ici (16 : ℝ),
        (ENNReal.ofReal (r ^ (Module.finrank ℝ LatticeSpace - 1) * W (r • θ.val)))⁻¹ := by
      apply setLIntegral_mono' measurableSet_Ici
      intro r hr
      have hr0 : (0:ℝ) < r := lt_of_lt_of_le (by norm_num) hr
      have hfin : Module.finrank ℝ LatticeSpace - 1 = 2 := by simp
      rw [hfin, one_div, ENNReal.ofReal_inv_of_pos (mul_pos (by positivity) (hW _))]
    _ ≤ ∫⁻ r in Ici (1 : ℝ),
        (ENNReal.ofReal (r ^ (Module.finrank ℝ LatticeSpace - 1) * W (r • θ.val)))⁻¹ :=
      lintegral_mono_set (Ici_subset_Ici.mpr (by norm_num))
    _ ≤ M := h

/-- Brown's ray test is silent on the lattice weight. -/
theorem lattice_ray_test_silent {α : ℝ} (hα : 4 ≤ α) :
    ¬ uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ))
        (sphereProbability (volume : Measure LatticeSpace))
        (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ LatticeSpace - 1) *
          latticeWeight latticeValleys α (r.val • θ.val))) :=
  ray_test_silent_of_divergent_rays (latticeWeight_pos latticeValleys α)
    (fun u hu => lattice_ray_integral_diverges hα u hu)

/-- Brown's ray test is also silent on the actual Gaussian marginal of the
lattice prior, by the two-sided comparison of `lem:lip`. -/
theorem lattice_marginal_ray_test_silent {α : ℝ≥0} (hα : 4 ≤ (α : ℝ)) :
    ¬ uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ))
        (sphereProbability (volume : Measure LatticeSpace))
        (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ LatticeSpace - 1) *
          gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys (α : ℝ))
            (r.val • θ.val))) := by
  obtain ⟨c, C, hc0, hc, hC0, hC, hlo, hhi⟩ := gaussian_comparable_ennreal
    (standardEuclideanGaussian (ι := Fin 3)) (latticeWeight_pos latticeValleys (α : ℝ))
    (latticeWeight_log_lipschitz latticeValleys α)
  intro hmarg
  apply lattice_ray_test_silent hα
  refine (uniformRayTest_iff_of_comparison _ _ hc0 hc hC0 hC ?_ ?_).mpr hmarg
  · intro r θ
    have hq : (0:ℝ) ≤ r.val ^ (Module.finrank ℝ LatticeSpace - 1) :=
      pow_nonneg (le_trans zero_le_one r.property) _
    rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_mul hq, mul_left_comm]
    exact mul_le_mul_left' (hlo _) _
  · intro r θ
    have hq : (0:ℝ) ≤ r.val ^ (Module.finrank ℝ LatticeSpace - 1) :=
      pow_nonneg (le_trans zero_le_one r.property) _
    rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_mul hq, mul_left_comm]
    exact mul_le_mul_left' (hhi _) _

end BrownRadial
