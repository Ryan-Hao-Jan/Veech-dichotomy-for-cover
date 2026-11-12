module

public import VeechDichotomy.BeltramiMarkedCoverTotalSpace

/-! The simultaneous varying-base moved total covering map is an actual
proper surjective holomorphic map with finite fibers. These assertions
refer to the constructed source topology and literal map, not a moduli
space or a postulated properness condition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedCoverFiniteMap

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedCoverTotalSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem projection_map (z : TotalSpace π F hBranch) :
    BeltramiMarkedReferenceSpace.projection A qX (map π F hBranch z) = projection π F hBranch z := rfl

theorem proper_map : IsProperMap (map π F hBranch) :=
  isProperMap_of_comp_of_t2 (holomorphic_map π F hBranch).continuous
    (BeltramiMarkedReferenceSpace.proper_projection A qX).continuous
    (show IsProperMap (BeltramiMarkedReferenceSpace.projection A qX ∘ map π F hBranch) from
      proper_projection π F hBranch)

theorem surjective_map : Function.Surjective (map π F hBranch) := by
  intro x
  obtain ⟨y, hy⟩ := π.surjective ((BeltramiMarkedBaseTransport.transported F x.point.1).symm x.point.2)
  refine ⟨(toProduct π F hBranch).symm (x.point.1, y), ?_⟩
  apply (BeltramiMarkedReferenceSpace.toProduct A qX).injective
  refine Prod.ext rfl ?_
  change BeltramiMarkedBaseTransport.transported F x.point.1 (π.map y) = x.point.2
  rw [hy]
  exact (BeltramiMarkedBaseTransport.transported F x.point.1).apply_symm_apply x.point.2

theorem finite_fibers (x : BeltramiMarkedReferenceSpace.TotalSpace A qX) :
    (map π F hBranch ⁻¹' {x}).Finite := by
  let H := BeltramiMarkedBaseTransport.transported F x.point.1
  apply ((π.finite_fibers (H.symm x.point.2)).image
    (fun y => (toProduct π F hBranch).symm (x.point.1, y))).subset
  intro z hz
  have hp := congrArg (fun w : BeltramiMarkedReferenceSpace.TotalSpace A qX => w.point.1) hz
  have hv := congrArg (fun w : BeltramiMarkedReferenceSpace.TotalSpace A qX => w.point.2) hz
  change (toProduct π F hBranch z).1 = x.point.1 at hp
  change BeltramiMarkedBaseTransport.transported F (toProduct π F hBranch z).1
    (π.map (toProduct π F hBranch z).2) = x.point.2 at hv
  rw [hp] at hv
  have hπ : π.map (toProduct π F hBranch z).2 = H.symm x.point.2 := by
    apply H.injective
    exact hv.trans (H.apply_symm_apply x.point.2).symm
  refine ⟨(toProduct π F hBranch z).2, hπ, ?_⟩
  apply (toProduct π F hBranch).injective
  exact Prod.ext hp.symm rfl

end VeechDichotomy.BeltramiMarkedCoverFiniteMap
