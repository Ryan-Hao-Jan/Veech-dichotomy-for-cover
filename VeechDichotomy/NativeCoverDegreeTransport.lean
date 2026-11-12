module

public import VeechDichotomy.NativeCoverEquivalence
public import VeechDichotomy.NativeDeformationBranchValues
public import VeechDichotomy.NativeFullCoverDegree

/-! Actual full sheet degree is preserved by native base equivalence
and native SL2 deformation. The proofs compare the genuine fibers over
an actual nonbranch reference point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverDegreeTransport

open MNEC.NativeAbelianDifferential NativeTranslationCover LinearGroup NativeDeformationRegular WholeDeformedAtlas Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {q : Differential X} {r : Differential Y} {s : Differential Z}

def postcomposeFiber (π : Cover q r) (e : MNEC.NativeDifferentialEquiv.Equiv q s) (x : X) :
    ((NativeCoverEquivalence.postcompose π e).map ⁻¹' {e.homeomorph x}) ≃ₜ (π.map ⁻¹' {x}) :=
  (Homeomorph.refl Y).subtype (p := fun y => y ∈ (NativeCoverEquivalence.postcompose π e).map ⁻¹' {e.homeomorph x})
    (q := fun y => y ∈ π.map ⁻¹' {x}) (fun _ => ⟨fun h => e.homeomorph.injective h, fun h => congrArg e.homeomorph h⟩)

theorem degree_postcompose (π : Cover q r) (e : MNEC.NativeDifferentialEquiv.Equiv q s) :
    NativeFullCoverDegree.degree (NativeCoverEquivalence.postcompose π e) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  have hx : e.homeomorph x.val ∉ branchValues (NativeCoverEquivalence.postcompose π e) := by
    rw [NativeCoverEquivalence.branchValues_postcompose]
    rintro ⟨z, hz, heq⟩
    exact x.property (e.homeomorph.injective heq ▸ hz)
  calc
    NativeFullCoverDegree.degree (NativeCoverEquivalence.postcompose π e) =
        Nat.card ((NativeCoverEquivalence.postcompose π e).map ⁻¹' {e.homeomorph x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hx).symm
    _ = Nat.card (π.map ⁻¹' {x.val}) := Nat.card_congr (postcomposeFiber π e x.val).toEquiv
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A : SL2) : ChartedSpace ℂ (WholeSurface r A) := WholeDeformedAtlas.chartedSpace r A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface r A) := WholeDeformedAtlas.isComplexManifold r A ω

def deformedFiber (π : Cover q r) (A : SL2) (x : X) :
    ((NativeDeformationCover.cover π A).map ⁻¹' {(toOriginal q A).symm x}) ≃ₜ (π.map ⁻¹' {x}) :=
  (toOriginal r A).subtype
    (p := fun y => y ∈ (NativeDeformationCover.cover π A).map ⁻¹' {(toOriginal q A).symm x})
    (q := fun y => y ∈ π.map ⁻¹' {x}) (by
      intro y
      constructor
      · exact fun h => congrArg WholeSurface.point h
      · exact fun h => congrArg (toOriginal q A).symm h)

theorem degree_deformation (π : Cover q r) (A : SL2) :
    NativeFullCoverDegree.degree (NativeDeformationCover.cover π A) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  have hx : (toOriginal q A).symm x.val ∉ branchValues (NativeDeformationCover.cover π A) := by
    rw [NativeDeformationBranchValues.branchValues_eq_image]
    rintro ⟨z, hz, heq⟩
    exact x.property ((toOriginal q A).symm.injective heq ▸ hz)
  calc
    NativeFullCoverDegree.degree (NativeDeformationCover.cover π A) =
        Nat.card ((NativeDeformationCover.cover π A).map ⁻¹' {(toOriginal q A).symm x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hx).symm
    _ = Nat.card (π.map ⁻¹' {x.val}) := Nat.card_congr (deformedFiber π A x.val).toEquiv
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

end VeechDichotomy.NativeCoverDegreeTransport
