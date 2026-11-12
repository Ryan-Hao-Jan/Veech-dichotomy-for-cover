module

public import VeechDichotomy.SL2BottomRowEndpoints
public import VeechDichotomy.NativeLatticeConjugation

/-! Every actual unit-circle endpoint is the bottom-row endpoint of
an explicit actual SL2 matrix. The actual affine inequalities are
equivalent to orbit-height comparisons in these coordinates, proving
ideal-end normalization without assuming a boundary action. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealEndpointHeightNormalization

open LinearGroup HyperbolicRegularCenters HyperbolicKleinHalfPlanes DirichletIdealRadialPoints
open SL2BottomRowEndpoints NativeLatticeConjugation
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem affine_nonpos_iff_height_le (B : SL2) (p q : ℍ) :
    affineForm p q (endpoint B) ≤ 0 ↔ (B • q).im ≤ (B • p).im := by
  rw [affine_endpoint, div_le_iff₀ (rowNormSq_pos B), zero_mul, sub_nonpos,
    height_formula, height_formula, div_le_div_iff₀ (denominatorSq_pos B q) (denominatorSq_pos B p)]

theorem ideal_iff_maximal_height (Γ : Subgroup SL2) (p : ℍ) (B : SL2) :
    endpoint B ∈ idealBoundary Γ p ↔ ∀ γ : Γ, (B • (γ • p)).im ≤ (B • p).im := by
  constructor
  · intro hu γ
    exact (affine_nonpos_iff_height_le B p (γ • p)).mp (closure_halfPlane Γ p hu.1 γ)
  · intro hh
    exact (DirichletClosedHalfPlanes.idealBoundary_iff Γ p _).mpr
      ⟨norm_endpoint B, fun γ => (affine_nonpos_iff_height_le B p (γ • p)).mpr (hh γ)⟩

theorem ideal_conjugate (Γ : Subgroup SL2) (p : ℍ) (B : SL2) (hu : endpoint B ∈ idealBoundary Γ p) :
    Complex.I ∈ idealBoundary (conjugate Γ B) (B • p) := by
  apply (DirichletIdealInfinity.mem_ideal_iff _ _).mpr
  intro δ
  let γ := toOriginal Γ B δ
  have hh := (ideal_iff_maximal_height Γ p B).mp hu γ
  have he : (δ : SL2) * B = B * (γ : SL2) := by dsimp only [γ, toOriginal]; group
  change ((δ : SL2) • (B • p)).im ≤ (B • p).im
  rw [← mul_smul, he, mul_smul]
  exact hh

theorem regular_conjugate (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (B : SL2) :
    RegularCenter (conjugate Γ B) (B • p) := by
  intro δ hδ z
  let γ := toOriginal Γ B δ
  have hγ : γ • p = p := by
    change (B⁻¹ * (δ : SL2) * B) • p = p
    rw [mul_smul, mul_smul]
    change B⁻¹ • (δ • (B • p)) = p
    rw [hδ, inv_smul_smul]
  have hid := hp γ hγ (B⁻¹ • z)
  calc
    δ • z = B • (γ • (B⁻¹ • z)) := by
      change (δ : SL2) • z = B • ((B⁻¹ * (δ : SL2) * B) • (B⁻¹ • z))
      simp only [mul_smul, smul_inv_smul]
    _ = z := by rw [hid, smul_inv_smul]

theorem exists_normalizer (u : ℂ) (hu : ‖u‖ = 1) : ∃ B : SL2, endpoint B = u := by
  by_cases hI : u = Complex.I
  · refine ⟨1, ?_⟩
    rw [hI]
    exact (ProjectiveRowBoundary.point_eq_I_iff _ _ (rowNormSq_pos 1)).mpr (by rfl)
  · let x := IdealBoundaryCoordinates.endpoint u
    let B : SL2 := ⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two]⟩
    have hBI : endpoint B ≠ Complex.I := by
      intro he
      have hz := (ProjectiveRowBoundary.point_eq_I_iff _ _ (rowNormSq_pos B)).mp he
      change (1 : ℝ) = 0 at hz
      norm_num at hz
    have he : IdealBoundaryCoordinates.endpoint (endpoint B) = IdealBoundaryCoordinates.endpoint u := by
      change IdealBoundaryCoordinates.endpoint (ProjectiveRowBoundary.point 1 (-x)) = x
      rw [ProjectiveRowBoundary.endpoint_point 1 (-x) (by positivity) one_ne_zero]
      ring
    exact ⟨B, IdealBoundaryCoordinates.endpoint_injective (norm_endpoint B) hu hBI hI he⟩

end VeechDichotomy.IdealEndpointHeightNormalization
