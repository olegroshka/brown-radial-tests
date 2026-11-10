import SphereTest
import RayTest
import RayToll
import LatticeVolume

/-!
Paper-facing statements for `paper/radial-tests.tex`, assembled from the
checked modules. Everything here is stated in the paper's potential-theoretic
vocabulary: "parabolic" is zero capacity of the unit ball, exactly as defined
in the Preliminaries. No statistical statement (admissibility) and no
recurrence statement for a diffusion is asserted anywhere in this file.

Where a paper result rests on a cited result that is not formalized, the
cited result is an explicit hypothesis of the Lean statement, never a new
foundation.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace BrownRadial

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Parabolicity in the paper's sense: the unit ball has zero capacity for
smooth compactly supported test functions. -/
def parabolic (w : E → ℝ) : Prop :=
  weightedCapacity μ (fun x => ENNReal.ofReal (w x)) (closedBall (0 : E) 1) = 0

/-- Brown's sphere test fires: the integral of `1 / (r^(m-1) fbar(r))` over
`[1, infinity)` diverges, `fbar` being the normalized spherical mean. -/
def sphereTestFires (w : E → ℝ) : Prop :=
  ¬ IntegrableOn (fun r : ℝ => 1 / (r ^ (Module.finrank ℝ E - 1) *
    ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ)) (Ici 1)

/-- The ball-volume test fires: the integral of `r / V(r)` diverges. -/
def volumeTestFires (w : E → ℝ) : Prop :=
  ¬ IntegrableOn (fun r => r / weightedBallVolume μ w r) (Ici 1)

/-- Brown's ray test fires: a set of directions of positive surface measure
has uniformly bounded ray integrals. -/
def rayTestFires (w : E → ℝ) : Prop :=
  uniformRayTest (volume.comap (Subtype.val : Ici (1 : ℝ) → ℝ)) (sphereProbability μ)
    (fun r θ => ENNReal.ofReal (r.val ^ (Module.finrank ℝ E - 1) * w (r.val • θ.val)))

theorem toSphere_real_univ_pos : 0 < μ.toSphere.real univ := by
  apply ENNReal.toReal_pos
  · exact Measure.measure_univ_ne_zero.mpr μ.toSphere_ne_zero
  · exact measure_ne_top _ _

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Integrals against the normalized sphere measure are the surface integrals
divided by the total surface measure. -/
theorem sphereProbability_integral (f : sphere (0 : E) 1 → ℝ) :
    ∫ θ, f θ ∂sphereProbability μ = (μ.toSphere.real univ)⁻¹ * ∫ θ, f θ ∂μ.toSphere := by
  unfold sphereProbability
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

/-- The spherical area is the total surface measure times `r^(m-1)` times the
normalized spherical mean, the quantity written `r^(m-1) fbar(r)` in the paper. -/
theorem sphericalArea_eq_mean (w : E → ℝ) (r : ℝ) :
    sphericalArea μ w r = μ.toSphere.real univ *
      (r ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ) := by
  have hpos := toSphere_real_univ_pos μ
  rw [sphereProbability_integral, sphericalArea]
  field_simp

/-- Convergence of the sphere integral does not depend on the normalization
of the surface measure. -/
theorem sphere_integrable_iff_mean (w : E → ℝ) :
    IntegrableOn (fun r => 1 / sphericalArea μ w r) (Ici 1) ↔
      IntegrableOn (fun r : ℝ => 1 / (r ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ)) (Ici 1) := by
  have hpos := toSphere_real_univ_pos μ
  have he : (fun r => 1 / sphericalArea μ w r) = fun r : ℝ =>
      (μ.toSphere.real univ)⁻¹ * (1 / (r ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ)) := by
    funext r
    rw [sphericalArea_eq_mean, one_div, one_div, mul_inv]
  rw [he]
  constructor
  · intro h
    have h2 := h.const_mul (μ.toSphere.real univ)
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] using h2
  · intro h
    exact h.const_mul _

theorem sphereTestFires_iff (w : E → ℝ) :
    sphereTestFires μ w ↔ ¬ IntegrableOn (fun r => 1 / sphericalArea μ w r) (Ici 1) := by
  unfold sphereTestFires
  rw [sphere_integrable_iff_mean]

/-- `cor:cs`: the sphere test dominates the volume test. -/
theorem volumeTest_implies_sphereTest {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (h : volumeTestFires μ w) : sphereTestFires μ w :=
  (sphereTestFires_iff μ w).mpr (sphere_volume_corollary μ hw hp h)

/-- `thm:brown`(d) in potential-theoretic form (the sphere-area test):
divergence of the sphere integral forces zero capacity. -/
theorem sphereTest_implies_parabolic {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (h : sphereTestFires μ w) : parabolic μ w :=
  sphere_test_capacity_zero μ hw hp ((sphereTestFires_iff μ w).mp h)

/-- The hypothesis-free direction of `thm:volume`: divergence of the volume
integral forces zero capacity. -/
theorem volumeTest_implies_parabolic {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (h : volumeTestFires μ w) : parabolic μ w :=
  volume_test_capacity_zero μ hw hp h

/-- `thm:brown`(e) in potential-theoretic form: the ray test forces positive
capacity. -/
theorem rayTest_implies_not_parabolic {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (h : rayTestFires μ w) : ¬ parabolic μ w :=
  (ray_test_capacity_pos μ hw hp h).ne'

/-- `thm:A`, the two implications (iii) => (ii) => (i). They hold for every
continuous positive weight, with no doubling or Poincare hypothesis and no
cited theorem. -/
theorem theorem_A_proved_implications {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) :
    (volumeTestFires μ w → sphereTestFires μ w) ∧ (sphereTestFires μ w → parabolic μ w) :=
  ⟨volumeTest_implies_sphereTest μ hw hp, sphereTest_implies_parabolic μ hw hp⟩

/-- `thm:A` as an equivalence, MODULO the cited heat-kernel direction of
`thm:volume` (parabolic implies divergence of the volume integral, which the
paper obtains for doubling and Poincare weights from Grigor'yan and
Saloff-Coste). That direction is the explicit hypothesis `hcited`; it is not
proved in this project. -/
theorem theorem_A_modulo_volume_criterion {w : E → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (hcited : parabolic μ w → volumeTestFires μ w) :
    (parabolic μ w ↔ sphereTestFires μ w) ∧ (sphereTestFires μ w ↔ volumeTestFires μ w) := by
  have h32 := volumeTest_implies_sphereTest μ hw hp
  have h21 := sphereTest_implies_parabolic μ hw hp
  exact ⟨⟨fun h => h32 (hcited h), h21⟩, ⟨fun h => hcited (h21 h), h32⟩⟩

/-- `lem:a2` in potential-theoretic form: for a bounded spherical A2 ratio the
two radial tests are exhaustive. If the sphere integral diverges the space is
parabolic; if it converges the ray test fires and the space is not parabolic. -/
theorem lemma_a2 {w : E → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) {C : ℝ}
    (hQ : ∀ r : ℝ, 1 ≤ r →
      (∫ θ : sphere (0 : E) 1, w (r • θ.val) ∂sphereProbability μ) *
      (∫ θ : sphere (0 : E) 1, 1 / w (r • θ.val) ∂sphereProbability μ) ≤ C) :
    (sphereTestFires μ w → parabolic μ w) ∧
      (¬ sphereTestFires μ w → rayTestFires μ w ∧ ¬ parabolic μ w) := by
  refine ⟨sphereTest_implies_parabolic μ hw hp, fun h => ?_⟩
  have hint := not_not.mp h
  have hray : rayTestFires μ w := spherical_A2_ray_test μ hw hp hQ hint
  exact ⟨hray, rayTest_implies_not_parabolic μ hw hp hray⟩

end General

section Lattice

/-- The displayed ray bound `(eq:raybound)` of the paper, with its constant
`2.62^(-alpha/2)`: in every shell `k >= 4` every ray pays at least
`2.62^(-alpha/2) * R^(alpha/2 - 2)` on an interval of length two around the
radius `R` of a lattice circle of that shell. -/
theorem lattice_ray_bound_displayed {α : ℝ} (hα : 0 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1)
    {k : ℕ} (hk : 4 ≤ k) :
    ∃ R : ℝ, (2:ℝ)^k ≤ R ∧ R + 4 ≤ (2:ℝ)^(k+1) ∧
      ENNReal.ofReal ((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) ≤
        ∫⁻ r in Icc (R-1) (R+1),
          ENNReal.ofReal (1 / (r^2 * latticeWeight latticeValleys α (r • u))) := by
  obtain ⟨R, hRlo, hRhi, hw⟩ := lattice_ray_weight_bound hα u hu hk
  refine ⟨R, hRlo, hRhi, ?_⟩
  have h16 : (16:ℝ) ≤ (2:ℝ)^k := by
    calc (16:ℝ) = (2:ℝ)^4 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hR16 : (16:ℝ) ≤ R := h16.trans hRlo
  have hRpos : 0 < R := by linarith
  have hApos : 0 < R ^ (α/2) := Real.rpow_pos_of_pos hRpos _
  have hKpos : 0 < (2.62:ℝ) ^ (α/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hB : ((2.62:ℝ)/R) ^ (α/2) = (2.62:ℝ) ^ (α/2) / R ^ (α/2) :=
    Real.div_rpow (by norm_num) hRpos.le _
  have hc : (2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2) =
      ((2.62:ℝ) ^ (α/2))⁻¹ * (R ^ (α/2) / R ^ 2) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_sub hRpos, Real.rpow_two]
  have hpt : ∀ r ∈ Icc (R-1) (R+1),
      ((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) / 2 ≤
        1 / (r^2 * latticeWeight latticeValleys α (r • u)) := by
    intro r hr
    have hrpos : 0 < r := by linarith [hr.1]
    have hwpos := latticeWeight_pos latticeValleys α (r • u)
    have hwle := hw r hr
    rw [hB] at hwle
    have hr2 : r^2 ≤ (R+1)^2 := pow_le_pow_left₀ hrpos.le hr.2 2
    have hden : r^2 * latticeWeight latticeValleys α (r • u) ≤
        (R+1)^2 * ((2.62:ℝ) ^ (α/2) / R ^ (α/2)) :=
      mul_le_mul hr2 hwle hwpos.le (by positivity)
    have hdenpos : 0 < r^2 * latticeWeight latticeValleys α (r • u) := by positivity
    refine le_trans ?_ (one_div_le_one_div_of_le hdenpos hden)
    rw [hc, le_div_iff₀ (by positivity)]
    have he : ((2.62:ℝ) ^ (α/2))⁻¹ * (R ^ (α/2) / R ^ 2) / 2 *
        ((R+1)^2 * ((2.62:ℝ) ^ (α/2) / R ^ (α/2))) = (R+1)^2 / (2 * R^2) := by
      field_simp
    rw [he, div_le_one (by positivity)]
    nlinarith
  have hcpos : 0 ≤ ((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) / 2 := by
    rw [hc]; positivity
  calc
    ENNReal.ofReal ((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) =
        ENNReal.ofReal (((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) / 2) *
          volume (Icc (R-1) (R+1)) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul hcpos]
      congr 1
      ring
    _ = ∫⁻ _ in Icc (R-1) (R+1),
        ENNReal.ofReal (((2.62:ℝ) ^ (-(α/2)) * R ^ (α/2 - 2)) / 2) :=
      (setLIntegral_const _ _).symm
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc
      (fun r hr => ENNReal.ofReal_le_ofReal (hpt r hr))

/-- `thm:B`(c): the weighted ball volume of the lattice weight grows like
`r^3`. The upper bound holds for all radii; the lower bound from radius 64. -/
theorem theorem_B_volume_growth {α : ℝ} (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 64 ≤ r →
      c * r^3 ≤ weightedBallVolume volume (latticeWeight latticeValleys α) r ∧
      weightedBallVolume volume (latticeWeight latticeValleys α) r ≤ (4/3) * Real.pi * r^3 := by
  obtain ⟨c, hc, hlow⟩ := lattice_volume_lower hα
  exact ⟨c, hc, fun r hr => ⟨hlow r hr, lattice_volume_upper hα (by linarith)⟩⟩

/-- `thm:B`(b) and the volume integral: on the lattice weight with
`alpha >= 4` the sphere test, the ray test and the volume test are all
silent. The sphere integral and the volume integral converge, and no set of
directions of positive measure has bounded ray integrals. -/
theorem theorem_B_tests_silent {α : ℝ} (hα : 4 ≤ α) :
    ¬ sphereTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys α) ∧
    ¬ rayTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys α) ∧
    ¬ volumeTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys α) := by
  have h0 : (0 : ℝ) ≤ α := by linarith
  refine ⟨fun h => ?_, lattice_ray_test_silent hα, fun h => ?_⟩
  · exact (sphereTestFires_iff _ _).mp h (lattice_sphere_integral_converges h0)
  · exact h (lattice_volume_integral_converges h0)

/-- `thm:B`(b), ray part, in the paper's strong form: the ray integral is
infinite along every direction. -/
theorem theorem_B_every_ray_diverges {α : ℝ} (hα : 4 ≤ α) (u : LatticeSpace) (hu : ‖u‖ = 1) :
    ∫⁻ r in Ici (16 : ℝ),
      ENNReal.ofReal (1 / (r ^ 2 * latticeWeight latticeValleys α (r • u))) = ⊤ :=
  lattice_ray_integral_diverges hα u hu

/-- The lattice weight and its Gaussian marginal have the same parabolicity
type (`lem:lip`(iv) for this weight). -/
theorem lattice_marginal_parabolic_iff (α : ℝ≥0) :
    parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys (α : ℝ)) ↔
      parabolic (volume : Measure LatticeSpace)
        (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys (α : ℝ))) := by
  unfold parabolic
  exact gaussian_capacity_zero_iff standardEuclideanGaussian volume
    (latticeWeight_pos latticeValleys (α : ℝ)) (latticeWeight_log_lipschitz latticeValleys α) _

/-- The conclusion of `thm:B` MODULO the cited volume criterion. The
hypothesis `hcited` is the heat-kernel direction of `thm:volume` for this
weight; the paper obtains it from part (a) (doubling and Poincare, not proved
in this project) and the cited theorems. Given it, the lattice weight and its
Gaussian marginal are not parabolic, although all radial tests are silent. -/
theorem theorem_B_not_parabolic_modulo_volume_criterion {α : ℝ≥0} (hα : 4 ≤ (α : ℝ))
    (hcited : parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys (α : ℝ)) →
      volumeTestFires (volume : Measure LatticeSpace) (latticeWeight latticeValleys (α : ℝ))) :
    ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys (α : ℝ)) ∧
      ¬ parabolic (volume : Measure LatticeSpace)
        (gaussianAverage standardEuclideanGaussian (latticeWeight latticeValleys (α : ℝ))) := by
  have h1 : ¬ parabolic (volume : Measure LatticeSpace) (latticeWeight latticeValleys (α : ℝ)) :=
    fun h => (theorem_B_tests_silent hα).2.2 (hcited h)
  exact ⟨h1, fun h => h1 ((lattice_marginal_parabolic_iff α).mpr h)⟩

end Lattice

end BrownRadial
