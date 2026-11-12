module

public import VeechDichotomy.BeltramiMarkedFiberDifferential
public import VeechDichotomy.NativeCoverBranchTopology
public import VeechDichotomy.BranchValuesUnderHomeomorph
public import VeechDichotomy.NativeFullCoverDegree

/-! Exact critical points, moved branch values and sheet degree of the
actual native fiber covers. These are derived from the literal map and
the proved local-injectivity characterization of native critical points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberBranchValues

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedFiberSurface BeltramiMarkedFiberDifferential
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (a : ComplexBeltramiMarkParameters.Parameters A)

def postHomeomorph : X ≃ₜ NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a) :=
  (BeltramiMarkedBaseTransport.transported F a).trans
    (NativeBeltramiSurface.toOriginal qX (BeltramiMarkedReferenceCharts.parameter A a)).symm

theorem critical_iff (y : Surface π F hBranch a) :
    y ∈ criticalSet (cover π F hBranch a) ↔ y.point ∈ criticalSet π := by
  rw [NativeCoverBranchTopology.critical_iff_not_locally_injective,
    NativeCoverBranchTopology.critical_iff_not_locally_injective]
  have hpost : (∃ U ∈ 𝓝 y, InjOn (cover π F hBranch a).map U) ↔
      ∃ U ∈ 𝓝 y, InjOn (π.map ∘ toOriginal π F hBranch a) U := by
    constructor
    · rintro ⟨U, hU, hi⟩
      refine ⟨U, hU, ?_⟩
      intro x hx z hz hxz
      exact hi hx hz (congrArg (postHomeomorph F a) hxz)
    · rintro ⟨U, hU, hi⟩
      refine ⟨U, hU, ?_⟩
      intro x hx z hz hxz
      exact hi hx hz ((postHomeomorph F a).injective hxz)
  exact not_congr (hpost.trans (BranchValuesUnderHomeomorph.locally_injective_precomp_iff π.map (toOriginal π F hBranch a) y))

theorem criticalSet_eq_preimage : criticalSet (cover π F hBranch a) = Surface.point ⁻¹' criticalSet π :=
  Set.ext (critical_iff π F hBranch a)

theorem branchValues_eq_image : branchValues (cover π F hBranch a) = postHomeomorph F a '' branchValues π := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨π.map y.point, ⟨y.point, (critical_iff π F hBranch a y).mp hy, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨⟨y⟩, (critical_iff π F hBranch a ⟨y⟩).mpr hy, rfl⟩

theorem branch_tuple : branchValues (cover π F hBranch a) = range (fun i => postHomeomorph F a (b i)) := by
  rw [branchValues_eq_image, ← hBranch, ← range_comp]
  rfl

theorem branch_section (i : Fin m) :
    NativeBeltramiFibers.inclusion qX (BeltramiMarkedReferenceCharts.parameter A a) (postHomeomorph F a (b i)) =
      UniformBeltramiMarkSections.sectionMap F i a := rfl

def fiberHomeomorph (x : X) :
    ((cover π F hBranch a).map ⁻¹' {postHomeomorph F a x}) ≃ₜ (π.map ⁻¹' {x}) :=
  (toOriginal π F hBranch a).subtype
    (p := fun y => y ∈ (cover π F hBranch a).map ⁻¹' {postHomeomorph F a x})
    (q := fun y => y ∈ π.map ⁻¹' {x}) (by
      intro y
      constructor
      · exact fun h => (postHomeomorph F a).injective h
      · exact fun h => congrArg (postHomeomorph F a) h)

theorem degree_eq : NativeFullCoverDegree.degree (cover π F hBranch a) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  have hnew : postHomeomorph F a x.val ∉ branchValues (cover π F hBranch a) := by
    rw [branchValues_eq_image]
    rintro ⟨z, hz, heq⟩
    exact x.property ((postHomeomorph F a).injective heq ▸ hz)
  calc
    NativeFullCoverDegree.degree (cover π F hBranch a) =
        Nat.card ((cover π F hBranch a).map ⁻¹' {postHomeomorph F a x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hnew).symm
    _ = Nat.card (π.map ⁻¹' {x.val}) := Nat.card_congr (fiberHomeomorph π F hBranch a x.val).toEquiv
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

end VeechDichotomy.BeltramiMarkedFiberBranchValues
