module

public import VeechDichotomy.NativeDeformationCover
public import VeechDichotomy.NativeCoverBranchTopology

/-! Simultaneous native SL2 deformation preserves the actual branch
points and branch values under the specified underlying homeomorphisms.
This follows from the proved analytic/topological branch-point identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationBranchValues

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationCover
open NativeCoverBranchTopology NativeDeformationRegular WholeDeformedAtlas LinearGroup
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

local instance (q : Differential X) (A : SL2) : ChartedSpace ℂ (WholeSurface q A) :=
  WholeDeformedAtlas.chartedSpace q A
local instance (q : Differential X) (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) :=
  WholeDeformedAtlas.isComplexManifold q A ω
local instance (q : Differential Y) (A : SL2) : ChartedSpace ℂ (WholeSurface q A) :=
  WholeDeformedAtlas.chartedSpace q A
local instance (q : Differential Y) (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) :=
  WholeDeformedAtlas.isComplexManifold q A ω

theorem locally_injective_iff (π : Cover ωX ωY) (A : SL2) (y : Y) :
    (∃ U ∈ 𝓝 ((toOriginal ωY A).symm y), InjOn (cover π A).map U) ↔
      ∃ V ∈ 𝓝 y, InjOn π.map V := by
  constructor
  · rintro ⟨U, hU, hinj⟩
    refine ⟨(toOriginal ωY A).symm ⁻¹' U, (toOriginal ωY A).symm.continuous.continuousAt hU, ?_⟩
    intro a ha b hb hab
    apply (toOriginal ωY A).symm.injective
    exact hinj ha hb (by simpa only [cover_map_value] using congrArg (toOriginal ωX A).symm hab)
  · rintro ⟨V, hV, hinj⟩
    refine ⟨toOriginal ωY A ⁻¹' V, ?_, ?_⟩
    · have ht : Tendsto (toOriginal ωY A) (𝓝 ((toOriginal ωY A).symm y)) (𝓝 y) := by
        simpa only [Homeomorph.apply_symm_apply] using
          ((toOriginal ωY A).continuous.continuousAt (x := (toOriginal ωY A).symm y)).tendsto
      exact ht hV
    · intro a ha b hb hab
      apply (toOriginal ωY A).injective
      apply hinj ha hb
      exact (toOriginal ωX A).symm.injective hab

theorem critical_at_lift_iff (π : Cover ωX ωY) (A : SL2) (y : Y) :
    (toOriginal ωY A).symm y ∈ criticalSet (cover π A) ↔ y ∈ criticalSet π := by
  rw [critical_iff_not_locally_injective, critical_iff_not_locally_injective]
  exact not_congr (locally_injective_iff π A y)

theorem criticalSet_eq_preimage (π : Cover ωX ωY) (A : SL2) :
    criticalSet (cover π A) = toOriginal ωY A ⁻¹' criticalSet π := by
  ext y
  simpa only [Homeomorph.symm_apply_apply, mem_preimage] using
    critical_at_lift_iff π A (toOriginal ωY A y)

theorem branchValues_eq_image (π : Cover ωX ωY) (A : SL2) :
    branchValues (cover π A) = (toOriginal ωX A).symm '' branchValues π := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨π.map (toOriginal ωY A y), ⟨toOriginal ωY A y, ?_, rfl⟩, rfl⟩
    rwa [criticalSet_eq_preimage] at hy
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨(toOriginal ωY A).symm y, (critical_at_lift_iff π A y).mpr hy, cover_map_value π A y⟩

theorem branch_tuple (π : Cover ωX ωY) (A : SL2) {m : ℕ} (b : Fin m → X)
    (hb : range b = branchValues π) :
    range (fun i => (toOriginal ωX A).symm (b i)) = branchValues (cover π A) := by
  rw [branchValues_eq_image, ← hb, ← range_comp]
  rfl

theorem distinct_marks (A : SL2) {m : ℕ} {b : Fin m → X} (hb : Function.Injective b) :
    Function.Injective (fun i => (toOriginal ωX A).symm (b i)) :=
  (toOriginal ωX A).symm.injective.comp hb

end VeechDichotomy.NativeDeformationBranchValues
