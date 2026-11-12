module

public import VeechDichotomy.SL2HyperbolicCoordinates

/-! A compact actual hyperbolic core and compact actual isotropy give
a compact subset of the actual right SL2 quotient. Every inverse
hyperbolic projection congruent to that core lies in this compact set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CompactHyperbolicCoreQuotient

open LinearGroup Set SL2HyperbolicCoordinates
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def coreGroup (K : Set ℍ) : Set SL2 := Inv.inv '' (homeomorph '' (K ×ˢ (univ : Set isotropy)))
def coreQuotient (Γ : Subgroup SL2) (K : Set ℍ) : Set (SL2 ⧸ Γ) := QuotientGroup.mk '' coreGroup K

theorem isCompact_coreGroup {K : Set ℍ} (hK : IsCompact K) : IsCompact (coreGroup K) :=
  ((hK.prod isCompact_univ).image homeomorph.continuous).image continuous_inv

theorem isCompact_coreQuotient (Γ : Subgroup SL2) {K : Set ℍ} (hK : IsCompact K) :
    IsCompact (coreQuotient Γ K) := (isCompact_coreGroup hK).image QuotientGroup.continuous_mk

theorem mem_coreQuotient (Γ : Subgroup SL2) (K : Set ℍ) (g : SL2) (γ : Γ) (z : ℍ)
    (hz : z ∈ K) (he : g⁻¹ • UpperHalfPlane.I = γ • z) :
    (QuotientGroup.mk g : SL2 ⧸ Γ) ∈ coreQuotient Γ K := by
  let H : SL2 := (γ : SL2)⁻¹ * g⁻¹
  have hH : H • UpperHalfPlane.I = z := by
    dsimp only [H]
    rw [mul_smul, he]
    exact inv_smul_smul (γ : SL2) z
  have hrep : homeomorph (z, coordinate H) = H := by
    have h := homeomorph.apply_symm_apply H
    change homeomorph (H • UpperHalfPlane.I, coordinate H) = H at h
    rwa [hH] at h
  have hgroup : H⁻¹ ∈ coreGroup K :=
    ⟨H, ⟨(z, coordinate H), ⟨hz, mem_univ _⟩, hrep⟩, rfl⟩
  have hq : (QuotientGroup.mk g : SL2 ⧸ Γ) = QuotientGroup.mk H⁻¹ := by
    apply QuotientGroup.eq.mpr
    have hprod : g⁻¹ * H⁻¹ = (γ : SL2) := by dsimp only [H]; group
    rw [hprod]
    exact γ.property
  exact ⟨H⁻¹, hgroup, hq.symm⟩

end VeechDichotomy.CompactHyperbolicCoreQuotient
