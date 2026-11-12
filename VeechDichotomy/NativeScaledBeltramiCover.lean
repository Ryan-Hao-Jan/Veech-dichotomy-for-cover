module

public import VeechDichotomy.NativeBeltramiCoverJoint
public import VeechDichotomy.NativeScaledBeltramiFamily

/-! Actual simultaneous finite covers over the scalar-extended analytic
families. The total map is proper and jointly holomorphic, including all
zero sections; the actual native fiber forms pull back exactly. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeScaledBeltramiCover

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeScaledBeltramiFamily Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY)

def cover (p : Base) : Cover (fiberForm ωX p) (fiberForm ωY p) where
  map := (NativeBeltramiCover.cover π p.2).map
  holomorphic := (NativeBeltramiCover.cover π p.2).holomorphic
  surjective := (NativeBeltramiCover.cover π p.2).surjective
  finite_fibers := (NativeBeltramiCover.cover π p.2).finite_fibers
  pullback_eq := by
    have h := (Jacobians.pullbackForm (NativeBeltramiCover.cover π p.2).map
      (NativeBeltramiCover.cover π p.2).holomorphic).map_smul p.1.val (NativeBeltramiDifferential.form ωX p.2).val
    exact h.trans (congrArg (fun α : Jacobians.HolomorphicOneForms (NativeBeltramiSurface.Surface ωY p.2) => p.1.val • α)
      (NativeBeltramiCover.cover π p.2).pullback_eq)

def map (p : Total ωY) : Total ωX := (p.1, NativeBeltramiCoverTotalMap.map π p.2)

theorem projection_map (p : Total ωY) : projection ωX (map π p) = projection ωY p := rfl

theorem holomorphic_map :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) ω (map π) :=
  contMDiff_id.prodMap (NativeBeltramiCoverJoint.holomorphic_map π)

theorem proper_map : IsProperMap (map π) := isProperMap_id.prodMap (NativeBeltramiCoverJoint.proper_map π)

theorem surjective_map : Function.Surjective (map π) := by
  intro p
  obtain ⟨y, hy⟩ := NativeBeltramiCoverTotalMap.surjective_map π p.2
  exact ⟨(p.1, y), Prod.ext rfl hy⟩

theorem finite_fibers (x : Total ωX) : (map π ⁻¹' {x}).Finite := by
  apply ((NativeBeltramiCoverTotalMap.finite_fibers π x.2).image (fun y => (x.1, y))).subset
  intro y hy
  exact ⟨y.2, congrArg Prod.snd hy, Prod.ext (congrArg Prod.fst hy).symm rfl⟩

theorem map_fiber (p : Base) (y : NativeBeltramiSurface.Surface ωY p.2) :
    map π (inclusion ωY p y) = inclusion ωX p ((cover π p).map y) := rfl

theorem branchValues_eq_image (p : Base) : branchValues (cover π p) =
    (NativeBeltramiSurface.toOriginal ωX p.2).symm '' branchValues π :=
  NativeBeltramiCoverBranchValues.branchValues_eq_image π p.2

theorem degree_eq (p : Base) : NativeFullCoverDegree.degree (cover π p) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference (NativeBeltramiCover.cover π p.2)
  have hx : x.val ∉ branchValues (cover π p) := x.property
  calc
    NativeFullCoverDegree.degree (cover π p) = Nat.card ((cover π p).map ⁻¹' {x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hx).symm
    _ = NativeFullCoverDegree.degree (NativeBeltramiCover.cover π p.2) :=
      NativeFullCoverDegree.fiber_card_eq_degree _ x.property
    _ = NativeFullCoverDegree.degree π := NativeBeltramiCoverBranchValues.degree_eq π p.2

end VeechDichotomy.NativeScaledBeltramiCover
