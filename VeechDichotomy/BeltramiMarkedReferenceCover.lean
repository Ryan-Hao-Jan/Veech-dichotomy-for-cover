module

public import VeechDichotomy.BeltramiMarkedReferenceMorphisms
public import VeechDichotomy.NativeBeltramiLocalCoverInverse

/-! The actual finite covering map in the marked reference families,
and its actual joint holomorphic local inverses off ramification.
All displacement coordinates are preserved literally. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedReferenceCover

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData BeltramiMarkedReferenceSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) (A : Data qX b μ₀)

def map (z : TotalSpace A qY) : TotalSpace A qX := ⟨(z.point.1, π.map z.point.2)⟩

theorem continuous_map : Continuous (map π A) :=
  (toProduct A qX).symm.continuous.comp
    ((continuous_fst.prodMk (π.holomorphic.continuous.comp continuous_snd)).comp (toProduct A qY).continuous)

theorem realization_map (z : TotalSpace A qY) :
    realization A qX (map π A z) = NativeBeltramiCoverTotalMap.map π (realization A qY z) := rfl

theorem holomorphic_map : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (map π A) := by
  intro z
  apply BeltramiMarkedReferenceMorphisms.holomorphicAt_of_realization A qX (map π A) z
  · exact (continuous_map π A).continuousAt
  · exact ambientParameter_holomorphic A qY z
  · exact (NativeBeltramiCoverJoint.holomorphic_map π _).comp z (realization_holomorphic A qY z)

def localMap (y : RelocatedCoverCharts.RegularPoint π) : OpenPartialHomeomorph (TotalSpace A qY) (TotalSpace A qX) :=
  ((toProduct A qY).transOpenPartialHomeomorph
    ((OpenPartialHomeomorph.refl (ComplexBeltramiMarkParameters.Parameters A)).prod
      (RelocatedCoverCharts.oldLocalMap π y))).transHomeomorph (toProduct A qX).symm

theorem localMap_apply (y : RelocatedCoverCharts.RegularPoint π) (z : TotalSpace A qY) :
    localMap π A y z = map π A z := by
  apply (toProduct A qX).injective
  refine Prod.ext rfl ?_
  exact RelocatedCoverCharts.localMap_apply π (Homeomorph.refl X) y z.point.2

theorem source_iff (y : RelocatedCoverCharts.RegularPoint π) (z : TotalSpace A qY) :
    z ∈ (localMap π A y).source ↔ z.point.2 ∈ (RelocatedCoverCharts.oldLocalMap π y).source := by
  change (_ ∈ univ ∧ _) ↔ _
  simp only [mem_univ, true_and]
  rfl

theorem target_iff (y : RelocatedCoverCharts.RegularPoint π) (z : TotalSpace A qX) :
    z ∈ (localMap π A y).target ↔ z.point.2 ∈ (RelocatedCoverCharts.oldLocalMap π y).target := by
  change (_ ∈ univ ∧ _) ↔ _
  simp only [mem_univ, true_and]
  rfl

theorem center_source (y : RelocatedCoverCharts.RegularPoint π) (a : ComplexBeltramiMarkParameters.Parameters A) :
    (⟨(a, y.val)⟩ : TotalSpace A qY) ∈ (localMap π A y).source :=
  (source_iff π A y _).mpr (RelocatedCoverCharts.localMap_center π (Homeomorph.refl X) y)

theorem holomorphic_localMap (y : RelocatedCoverCharts.RegularPoint π) :
    ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (localMap π A y) := by
  intro z
  apply (holomorphic_map π A z).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (localMap_apply π A y)

theorem inverse_holomorphicAt (y : RelocatedCoverCharts.RegularPoint π) {x : TotalSpace A qX}
    (hx : x ∈ (localMap π A y).target) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (localMap π A y).symm x := by
  have hntarget : realization A qX x ∈ (NativeBeltramiLocalCoverInverse.localMap π y).target := by
    change (_ ∈ univ ∧ x.point.2 ∈ (RelocatedCoverCharts.oldLocalMap π y).target)
    exact ⟨mem_univ _, (target_iff π A y x).mp hx⟩
  have hInv := (NativeBeltramiLocalCoverInverse.inverse_holomorphicOn π y).contMDiffAt
    ((NativeBeltramiLocalCoverInverse.localMap π y).open_target.mem_nhds hntarget)
  apply BeltramiMarkedReferenceMorphisms.holomorphicAt_of_realization A qY (localMap π A y).symm x
  · exact (localMap π A y).symm.continuousAt hx
  · exact ambientParameter_holomorphic A qX x
  · exact hInv.comp x (realization_holomorphic A qX x)

end VeechDichotomy.BeltramiMarkedReferenceCover
