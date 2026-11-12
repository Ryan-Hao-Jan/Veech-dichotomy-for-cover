module

public import VeechDichotomy.NativeDeformationCancellation
public import VeechDichotomy.NativeCoverDegreeTransport
public import VeechDichotomy.NativeCoverIsomorphism

/-! An actual cover of a native SL2-deformed base can be returned to
the original base by the GIVEN inverse matrix. Deforming it back recovers
the original actual cover by an explicit native differential equivalence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverUndeformation

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) {r : Differential Y}

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed q A) B) := WholeDeformedAtlas.chartedSpace (transformed q A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed q A) B) := WholeDeformedAtlas.isComplexManifold (transformed q A) B ω
local instance (A : SL2) : ChartedSpace ℂ (WholeSurface r A) := WholeDeformedAtlas.chartedSpace r A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface r A) := WholeDeformedAtlas.isComplexManifold r A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed r A) B) := WholeDeformedAtlas.chartedSpace (transformed r A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed r A) B) := WholeDeformedAtlas.isComplexManifold (transformed r A) B ω

def cover (L : SL2) (ρ : Cover (transformed q L) r) : Cover q (transformed r L⁻¹) :=
  NativeCoverEquivalence.postcompose (NativeDeformationCover.cover ρ L⁻¹)
    (NativeDeformationCancellation.equivalence q L L⁻¹ (inv_mul_cancel L))

theorem map_value (L : SL2) (ρ : Cover (transformed q L) r) (y : WholeSurface r L⁻¹) :
    (cover q L ρ).map y = toOriginal q L (ρ.map y.point) := rfl

theorem degree_eq (L : SL2) (ρ : Cover (transformed q L) r) :
    NativeFullCoverDegree.degree (cover q L ρ) = NativeFullCoverDegree.degree ρ :=
  (NativeCoverDegreeTransport.degree_postcompose _ _).trans (NativeCoverDegreeTransport.degree_deformation ρ L⁻¹)

theorem branch_values (L : SL2) (ρ : Cover (transformed q L) r) :
    branchValues (cover q L ρ) = toOriginal q L '' branchValues ρ := by
  rw [cover, NativeCoverEquivalence.branchValues_postcompose, NativeDeformationBranchValues.branchValues_eq_image, image_image]
  apply image_congr
  intro x _
  rfl

abbrev recoveredCover (L : SL2) (ρ : Cover (transformed q L) r) := NativeDeformationCover.cover (cover q L ρ) L

def recoveryEquivalence (L : SL2) (ρ : Cover (transformed q L) r) :
    MNEC.NativeDifferentialEquiv.Equiv (transformed (transformed r L⁻¹) L) r :=
  NativeCoverIsomorphism.equivalence_of_commutes (recoveredCover q L ρ) ρ
    (NativeDeformationCancellation.sourceHomeomorph r L⁻¹ L) (by intro y; rfl)

theorem recovery_commutes (L : SL2) (ρ : Cover (transformed q L) r) (y : WholeSurface (transformed r L⁻¹) L) :
    ρ.map ((recoveryEquivalence q L ρ).homeomorph y) = (recoveredCover q L ρ).map y := rfl

end VeechDichotomy.NativeCoverUndeformation
