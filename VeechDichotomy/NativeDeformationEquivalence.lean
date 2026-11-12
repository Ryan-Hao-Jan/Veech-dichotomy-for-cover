module

public import VeechDichotomy.NativeDeformationCover
public import VeechDichotomy.NativeDifferentialEquivalenceLaws

/-! Native SL2 deformation transports genuine native differential
equivalences, retaining their explicit whole-curve homeomorphisms.
Actual commuting covering squares remain commuting after deformation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationEquivalence

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup Set
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

def asCover (e : MNEC.NativeDifferentialEquiv.Equiv q r) : Cover r q where
  map := e.homeomorph
  holomorphic := HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable
  surjective := e.homeomorph.surjective
  finite_fibers y := (finite_singleton (e.homeomorph.symm y)).subset (by
    intro x hx
    have h := e.homeomorph.symm_apply_apply x
    rw [hx] at h
    exact h.symm)
  pullback_eq := by
    apply ContMDiffSection.ext
    intro x
    exact (e.oneForm_pullback x).symm

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A : SL2) : ChartedSpace ℂ (WholeSurface r A) := WholeDeformedAtlas.chartedSpace r A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface r A) := WholeDeformedAtlas.isComplexManifold r A ω
local instance (A : SL2) : ChartedSpace ℂ (WholeSurface s A) := WholeDeformedAtlas.chartedSpace s A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface s A) := WholeDeformedAtlas.isComplexManifold s A ω

def sourceHomeomorph (e : MNEC.NativeDifferentialEquiv.Equiv q r) (A : SL2) : WholeSurface q A ≃ₜ WholeSurface r A :=
  ((toOriginal q A).trans e.homeomorph).trans (toOriginal r A).symm

def equivalence (e : MNEC.NativeDifferentialEquiv.Equiv q r) (A : SL2) :
    MNEC.NativeDifferentialEquiv.Equiv (transformed q A) (transformed r A) where
  homeomorph := sourceHomeomorph e A
  differentiable x := (NativeDeformationCover.cover (asCover e) A).holomorphic.mdifferentiableAt (by decide)
  inverse_differentiable y := (NativeDeformationCover.cover (asCover (NativeDifferentialEquivalenceLaws.symm e)) A).holomorphic.mdifferentiableAt (by decide)
  oneForm_pullback x := NativeTranslationCover.pullback_at (NativeDeformationCover.cover (asCover e) A) x

theorem cover_square (π : Cover s q) (ρ : Cover s r) (e : MNEC.NativeDifferentialEquiv.Equiv q r)
    (hsquare : ∀ y, ρ.map (e.homeomorph y) = π.map y) (A : SL2) (y : WholeSurface q A) :
    (NativeDeformationCover.cover ρ A).map ((equivalence e A).homeomorph y) = (NativeDeformationCover.cover π A).map y := by
  change (toOriginal s A).symm (ρ.map (e.homeomorph y.point)) = (toOriginal s A).symm (π.map y.point)
  exact congrArg (toOriginal s A).symm (hsquare y.point)

end VeechDichotomy.NativeDeformationEquivalence
