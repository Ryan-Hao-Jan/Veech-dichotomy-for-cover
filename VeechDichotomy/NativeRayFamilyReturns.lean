module

public import VeechDichotomy.NativeNormalizedCoverReturns
public import VeechDichotomy.NativeTeichmullerRay

/-! Concrete analytic-family returns of the ACTUAL contracting native
ray. At the selected times, its vertical flow is still minimal, its area
is the original area, and the tested velocity contracts to zero. The base
quotient return hypothesis remains explicit; no lattice or Masur theorem
is asserted here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayFamilyReturns

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup NativeVeech
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y}

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qX B) := WholeDeformedAtlas.chartedSpace qX B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qX B) := WholeDeformedAtlas.isComplexManifold qX B ω
local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qY B) := WholeDeformedAtlas.chartedSpace qY B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qY B) := WholeDeformedAtlas.isComplexManifold qY B ω

theorem from_returns (π : Cover qX qY) {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hCi : invariant (NativeAffineGroup.AffineGroup qX) C)
    (hbC : b ∈ C) (hconf : C ⊆ configuration m X) (v : Plane) (hv : v ≠ 0)
    (hminimal : NativeDynamics.MinimalDirection qY v)
    (hreturns : HasCompactReturns (fun t =>
      (QuotientGroup.mk (NativeTeichmullerRay.matrix v hv t) : SL2 ⧸ derivativeGroup qX))) :
    ∃ t : ℕ → ℝ, StrictMono t ∧ Tendsto t atTop atTop ∧
      Tendsto (fun n => NativeTeichmullerRay.contraction v (t n)) atTop (𝓝 0) ∧
      (∀ n, NativeDynamics.MinimalDirection (NativeTeichmullerRay.rayForm qY v hv (t n)) NativeTeichmullerRay.vertical) ∧
      (∀ n, MNEC.NativeFiniteRegularArea.totalArea (NativeTeichmullerRay.rayForm qY v hv (t n)) = MNEC.NativeFiniteRegularArea.totalArea qY) ∧
      ∃ K : Set SL2, IsCompact K ∧ ∃ γ : ℕ → SL2, ∃ φ : ∀ n, AffineAutomorphism qX (γ n),
        (∀ n, NativeNormalizedCoverSequences.matrix (NativeTeichmullerRay.matrix v hv ∘ t) γ n ∈ K) ∧
        (∀ n, NativeNormalizedCoverSequences.branches b φ n ∈ C) ∧
        NativeCoverFamilyLimits.FamilyLimit (fun n => WholeSurface qY (NativeTeichmullerRay.matrix v hv (t n)))
          (NativeNormalizedCoverSequences.matrix (NativeTeichmullerRay.matrix v hv ∘ t) γ)
          (NativeNormalizedCoverSequences.branches b φ) (fun n => NativeTeichmullerRay.rayForm qY v hv (t n))
          (NativeNormalizedCoverSequences.cover π (NativeTeichmullerRay.matrix v hv ∘ t) γ φ)
          (NativeNormalizedCoverSequences.branch_tuple π (NativeTeichmullerRay.matrix v hv ∘ t) γ φ b hb) K C := by
  obtain ⟨t, ht, htlim, K, hK, γ, φ, hmat, hmarks, hlimit⟩ :=
    NativeNormalizedCoverReturns.from_returns π b hb hC hCi hbC hconf (NativeTeichmullerRay.matrix v hv) hreturns
  exact ⟨t, ht, htlim, (NativeTeichmullerRay.contraction_tendsto_zero v).comp htlim,
    (fun n => (NativeTeichmullerRay.minimal_vertical_iff qY v hv (t n)).mp hminimal),
    (fun n => NativeTeichmullerRay.totalArea_constant qY v hv (t n)), K, hK, γ, φ, hmat, hmarks, hlimit⟩

end VeechDichotomy.NativeRayFamilyReturns
