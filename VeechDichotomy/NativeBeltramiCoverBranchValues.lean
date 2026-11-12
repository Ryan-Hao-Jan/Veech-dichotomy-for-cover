module

public import VeechDichotomy.NativeBeltramiCover
public import VeechDichotomy.NativeBeltramiMarkedSections
public import VeechDichotomy.NativeCoverBranchTopology
public import VeechDichotomy.BranchValuesUnderHomeomorph
public import VeechDichotomy.NativeFullCoverDegree

/-! Simultaneous native unit-disk deformation preserves the actual
critical points, branch values and degree. The branch marks lie on the
constructed holomorphic fixed-point sections of the base family. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverBranchValues

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCover
open BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (μ : Parameter)

theorem critical_iff (y : NativeBeltramiSurface.Surface ωY μ) :
    y ∈ criticalSet (cover π μ) ↔ y.point ∈ criticalSet π := by
  rw [NativeCoverBranchTopology.critical_iff_not_locally_injective,
    NativeCoverBranchTopology.critical_iff_not_locally_injective]
  have hpost : (∃ U ∈ 𝓝 y, InjOn (cover π μ).map U) ↔
      ∃ U ∈ 𝓝 y, InjOn (π.map ∘ NativeBeltramiSurface.toOriginal ωY μ) U := by
    constructor
    · rintro ⟨U, hU, hi⟩
      refine ⟨U, hU, ?_⟩
      intro a ha b hb hab
      exact hi ha hb (congrArg (NativeBeltramiSurface.toOriginal ωX μ).symm hab)
    · rintro ⟨U, hU, hi⟩
      refine ⟨U, hU, ?_⟩
      intro a ha b hb hab
      exact hi ha hb (congrArg (NativeBeltramiSurface.toOriginal ωX μ) hab)
  exact not_congr (hpost.trans (BranchValuesUnderHomeomorph.locally_injective_precomp_iff π.map
    (NativeBeltramiSurface.toOriginal ωY μ) y))

theorem criticalSet_eq_preimage : criticalSet (cover π μ) =
    NativeBeltramiSurface.Surface.point ⁻¹' criticalSet π := Set.ext (critical_iff π μ)

theorem branchValues_eq_image : branchValues (cover π μ) =
    (NativeBeltramiSurface.toOriginal ωX μ).symm '' branchValues π := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨π.map y.point, ⟨y.point, (critical_iff π μ y).mp hy, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨⟨y⟩, (critical_iff π μ ⟨y⟩).mpr hy, rfl⟩

theorem branch_tuple {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π) :
    branchValues (cover π μ) = range (fun i => (NativeBeltramiSurface.toOriginal ωX μ).symm (b i)) := by
  rw [branchValues_eq_image, ← hb, ← range_comp]
  rfl

theorem branch_section {m : ℕ} (b : Fin m → X) (i : Fin m) :
    NativeBeltramiFibers.inclusion ωX μ ((NativeBeltramiSurface.toOriginal ωX μ).symm (b i)) =
      NativeBeltramiMarkedSections.sectionMap ωX (b i) μ := rfl

def fiberHomeomorph (x : X) :
    ((cover π μ).map ⁻¹' {(NativeBeltramiSurface.toOriginal ωX μ).symm x}) ≃ₜ (π.map ⁻¹' {x}) :=
  (NativeBeltramiSurface.toOriginal ωY μ).subtype
    (p := fun y => y ∈ (cover π μ).map ⁻¹' {(NativeBeltramiSurface.toOriginal ωX μ).symm x})
    (q := fun y => y ∈ π.map ⁻¹' {x}) (by
      intro y
      constructor
      · exact fun h => congrArg (NativeBeltramiSurface.toOriginal ωX μ) h
      · exact fun h => (NativeBeltramiSurface.toOriginal ωX μ).injective h)

theorem degree_eq : NativeFullCoverDegree.degree (cover π μ) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  have hnew : (NativeBeltramiSurface.toOriginal ωX μ).symm x.val ∉ branchValues (cover π μ) := by
    rw [branchValues_eq_image]
    rintro ⟨y, hy, heq⟩
    exact x.property ((NativeBeltramiSurface.toOriginal ωX μ).symm.injective heq ▸ hy)
  calc
    NativeFullCoverDegree.degree (cover π μ) =
        Nat.card ((cover π μ).map ⁻¹' {(NativeBeltramiSurface.toOriginal ωX μ).symm x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hnew).symm
    _ = Nat.card (π.map ⁻¹' {x.val}) := Nat.card_congr (fiberHomeomorph π μ x.val).toEquiv
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

end VeechDichotomy.NativeBeltramiCoverBranchValues
