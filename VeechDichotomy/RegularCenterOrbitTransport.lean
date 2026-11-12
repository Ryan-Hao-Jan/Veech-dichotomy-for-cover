module

public import VeechDichotomy.HyperbolicRegularCenters

/-! Actual regular-center stabilizer triviality is preserved along the
actual group orbit, including the ineffective central kernel. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RegularCenterOrbitTransport

open LinearGroup HyperbolicRegularCenters
open scoped UpperHalfPlane

theorem smul_regular (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (γ : Γ) :
    RegularCenter Γ (γ • p) := by
  intro δ hδ z
  let η : Γ := γ⁻¹ * δ * γ
  have hη : η • p = p := by
    dsimp only [η]
    rw [mul_smul, mul_smul, hδ, inv_smul_smul]
  have hid := hp η hη (γ⁻¹ • z)
  calc
    δ • z = γ • (η • (γ⁻¹ • z)) := by
      dsimp only [η]
      simp only [mul_smul, smul_inv_smul]
    _ = z := by rw [hid, smul_inv_smul]

end VeechDichotomy.RegularCenterOrbitTransport
