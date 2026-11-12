module

public import VeechDichotomy.HyperbolicDirichletTessellation

/-! Actual incidence between Dirichlet tiles is characterized by equal
nearest-center distances. On the actual base region, a label's tile
contains a point exactly when that label's center is equidistant with
the base center. Compact sets therefore involve finitely many actual
active labels, by the proved locally finite tessellation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletIncidence

open LinearGroup HyperbolicDirichletRegions HyperbolicDirichletTessellation Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

variable (Γ : Subgroup SL2)

theorem inverse_smul_distance (γ : Γ) (w q : ℍ) :
    dist (γ⁻¹ • w) q = dist w (γ • q) := by
  change dist ((γ : SL2)⁻¹ • w) q = dist w ((γ : SL2) • q)
  simpa only [inv_smul_smul] using dist_smul ((γ : SL2)⁻¹) w ((γ : SL2) • q)

theorem mem_tile_iff (p : ℍ) (γ : Γ) (w : ℍ) (hw : w ∈ region Γ p) :
    w ∈ tile Γ p γ ↔ dist w p = dist w (γ • p) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply le_antisymm (hw γ)
    have h := hz γ⁻¹
    have hm : dist z (γ⁻¹ • p) = dist (γ • z) p := by
      change dist z ((γ : SL2)⁻¹ • p) = dist ((γ : SL2) • z) p
      simpa only [smul_inv_smul] using (dist_smul (γ : SL2) z ((γ : SL2)⁻¹ • p)).symm
    rw [hm] at h
    change dist ((γ : SL2) • z) ((γ : SL2) • p) ≤ dist ((γ : SL2) • z) p
    rw [dist_smul]
    exact h
  · intro heq
    refine ⟨γ⁻¹ • w, ?_, smul_inv_smul γ w⟩
    intro δ
    rw [inverse_smul_distance, inverse_smul_distance, ← heq]
    simpa only [mul_smul] using hw (γ * δ)

def activeLabels (p : ℍ) (K : Set ℍ) : Set Γ :=
  {γ | ∃ w ∈ K, w ∈ region Γ p ∧ dist w p = dist w (γ • p)}

theorem activeLabels_finite [DiscreteTopology Γ] (p : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    (activeLabels Γ p K).Finite := by
  apply (finite_inter_compact Γ p hK).subset
  rintro γ ⟨w, hwK, hwD, heq⟩
  exact ⟨w, (mem_tile_iff Γ p γ w hwD).mpr heq, hwK⟩

end VeechDichotomy.HyperbolicDirichletIncidence
