module

public import VeechDichotomy.RelocatedCoverDifferential
public import VeechDichotomy.BranchValuesUnderHomeomorph
public import VeechDichotomy.NativeCoverIsomorphism

/-! The newly constructed native cover has precisely the actual moved
branch values, including ramification over zeros. At identity base
transport it is genuinely equivalent to the original native cover.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverBranchValues

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverAtlas
open RelocatedCoverDifferential Set Filter Topology Jacobians.Discharge.Manifold
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

local instance : ChartedSpace ℂ (Surface π ψ hψ hInv) := RelocatedCoverAtlas.chartedSpace π ψ hψ hInv
local instance : IsManifold 𝓘(ℂ) ω (Surface π ψ hψ hInv) := RelocatedCoverAtlas.isComplexManifold π ψ hψ hInv ω

theorem criticalSet_eq_topological :
    criticalSet (cover π ψ hψ hInv) = criticalSetGeneral (RelocatedCoverProjection.map π ψ hψ hInv) := by
  ext i
  exact NativeCoverBranchTopology.critical_iff_not_locally_injective (cover π ψ hψ hInv) i

theorem criticalSet_eq_preimage :
    criticalSet (cover π ψ hψ hInv) = (toOriginal π ψ hψ hInv) ⁻¹' criticalSet π := by
  rw [criticalSet_eq_topological]
  change criticalSetGeneral (RelocatedCoverCharts.projection π ψ ∘ toOriginal π ψ hψ hInv) = _
  rw [BranchValuesUnderHomeomorph.criticalSet_precomp, NativeMovingCoverMap.topologicalCriticalSet_eq]

theorem branchValues_eq_image : branchValues (cover π ψ hψ hInv) = ψ '' branchValues π := by
  have hv : branchValues (cover π ψ hψ hInv) =
      criticalValuesGeneral (RelocatedCoverProjection.map π ψ hψ hInv) := by
    change (RelocatedCoverProjection.map π ψ hψ hInv) '' criticalSet (cover π ψ hψ hInv) = _
    rw [criticalSet_eq_topological]
    rfl
  rw [hv]
  change criticalValuesGeneral (RelocatedCoverCharts.projection π ψ ∘ toOriginal π ψ hψ hInv) = _
  rw [BranchValuesUnderHomeomorph.criticalValues_precomp, NativeMovingCoverMap.topologicalBranchValues_eq]

theorem branch_tuple {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π) :
    range (fun i => ψ (b i)) = branchValues (cover π ψ hψ hInv) := by
  rw [branchValues_eq_image, ← hb, ← range_comp]
  rfl

def equivalence_at_identity (hId : ψ = Homeomorph.refl X) :
    MNEC.NativeDifferentialEquiv.Equiv (form π ψ hψ hInv) ωY :=
  NativeCoverIsomorphism.equivalence_of_commutes (cover π ψ hψ hInv) π
    (toOriginal π ψ hψ hInv) (by
      intro i
      change π.map i.point = ψ (π.map i.point)
      exact (congrArg (fun H : X ≃ₜ X => H (π.map i.point)) hId).symm)

end VeechDichotomy.RelocatedCoverBranchValues
