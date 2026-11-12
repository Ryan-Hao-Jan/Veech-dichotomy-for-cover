module

public import VeechDichotomy.BeltramiMarkedReferenceCover
public import VeechDichotomy.BeltramiMarkedTransportRegularity
public import VeechDichotomy.HolomorphicCoverRelocationData

/-! Every input of source-atlas relocation is derived for the actual
native varying-base marked cover. In particular, the local inverses and
transport germs are the proved native maps, and the entire critical set
is covered even when a branch point is a differential zero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRelocationData

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedReferenceSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def data : HolomorphicCoverRelocationData.Data
    (E := ComplexBeltramiMarkParameters.Space (m := m) × ℂ) (M := TotalSpace A qY) (N := TotalSpace A qX) where
  map := BeltramiMarkedReferenceCover.map π A
  holomorphic := BeltramiMarkedReferenceCover.holomorphic_map π A
  transport := BeltramiMarkedBaseTransport.homeomorph F
  region := ⋃ i, BeltramiMarkedBaseTransport.region (A := A) i
  region_open := isOpen_iUnion fun i => BeltramiMarkedBaseTransport.region_open i
  transport_holomorphic := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact BeltramiMarkedTransportRegularity.forward_holomorphicAt F i hi
  inverse_holomorphic := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact BeltramiMarkedTransportRegularity.inverse_holomorphicAt F i hi
  critical := {z | z.point.2 ∈ criticalSet π}
  critical_region := by
    intro z hz
    have hb : π.map z.point.2 ∈ range b := by
      rw [hBranch]
      exact ⟨z.point.2, hz, rfl⟩
    obtain ⟨i, hi⟩ := hb
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have hpoint : BeltramiMarkedReferenceCover.map π A z = (⟨(z.point.1, b i)⟩ : TotalSpace A qX) := by
      apply (toProduct A qX).injective
      exact Prod.ext rfl hi.symm
    rw [hpoint]
    exact BeltramiMarkedBaseTransport.center_region z.point.1 i
  localMap := fun z => BeltramiMarkedReferenceCover.localMap π A ⟨z.val.point.2, z.property⟩
  local_center := by
    intro z
    apply (BeltramiMarkedReferenceCover.source_iff π A ⟨z.val.point.2, z.property⟩ z.val).mpr
    exact RelocatedCoverCharts.localMap_center π (Homeomorph.refl X) ⟨z.val.point.2, z.property⟩
  local_apply := fun z w => BeltramiMarkedReferenceCover.localMap_apply π A ⟨z.val.point.2, z.property⟩ w
  local_inverse := fun z w hw => BeltramiMarkedReferenceCover.inverse_holomorphicAt π A ⟨z.val.point.2, z.property⟩ hw

end VeechDichotomy.BeltramiMarkedRelocationData
