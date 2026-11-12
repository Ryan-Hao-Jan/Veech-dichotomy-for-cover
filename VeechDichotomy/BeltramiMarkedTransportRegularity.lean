module

public import VeechDichotomy.BeltramiMarkedBaseTransport

/-! The actual total-space transport and inverse are jointly holomorphic
on the marked inner regions and their images. All germ formulas are
identified with the actual reference total-space homeomorphism. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedTransportRegularity

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedReferenceSpace
open BeltramiMarkedBaseTransport UniformBeltramiTransportFormulas
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter} {A : Data qX b μ₀} (F : Family A)

theorem forward_realization (i : Fin m) (z : TotalSpace A qX) (hz : z ∈ chartSource (A := A) i) :
    realization A qX (homeomorph F z) = ambientForward F i (z.point.1.val, coordinate (A := A) i z) := by
  let p := ComplexBeltramiMarkParameters.productHomeomorph A z.point.1
  have hp : ambientParameters (A := A) z.point.1.val = p := by
    change ComplexBeltramiMarkParameters.productHomeomorph A
      ((ComplexBeltramiMarkParameters.chart A).symm ((ComplexBeltramiMarkParameters.chart A) z.point.1)) = p
    rw [(ComplexBeltramiMarkParameters.chart A).left_inv (mem_univ z.point.1)]
  rw [ambientForward, hp]
  apply (NativeBeltramiTotalSpace.toProduct qX).injective
  refine Prod.ext rfl ?_
  have hx : (⟨z.point.2⟩ : NativeBeltramiSurface.Surface qX p.1.val) ∈ (F.disks p.1 i).chart.source := hz
  have h := congrArg NativeBeltramiSurface.Surface.point ((F.disks p.1 i).chart.left_inv hx)
  exact congrArg (F.map p) h.symm

theorem inverse_realization (i : Fin m) (z : TotalSpace A qX) (hz : z ∈ chartSource (A := A) i) :
    realization A qX ((homeomorph F).symm z) = ambientInverse F i (z.point.1.val, coordinate (A := A) i z) := by
  let p := ComplexBeltramiMarkParameters.productHomeomorph A z.point.1
  have hp : ambientParameters (A := A) z.point.1.val = p := by
    change ComplexBeltramiMarkParameters.productHomeomorph A
      ((ComplexBeltramiMarkParameters.chart A).symm ((ComplexBeltramiMarkParameters.chart A) z.point.1)) = p
    rw [(ComplexBeltramiMarkParameters.chart A).left_inv (mem_univ z.point.1)]
  rw [ambientInverse, hp]
  apply (NativeBeltramiTotalSpace.toProduct qX).injective
  refine Prod.ext rfl ?_
  have hx : (⟨z.point.2⟩ : NativeBeltramiSurface.Surface qX p.1.val) ∈ (F.disks p.1 i).chart.source := hz
  have h := congrArg NativeBeltramiSurface.Surface.point ((F.disks p.1 i).chart.left_inv hx)
  exact congrArg (F.map p).symm h.symm

theorem forward_holomorphicAt (i : Fin m) {z : TotalSpace A qX} (hz : z ∈ region (A := A) i) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (homeomorph F) z := by
  have hinput := (ambientParameter_holomorphic A qX z).prodMk_space (coordinate_holomorphicAt i hz.1)
  have hg := UniformBeltramiTransportGerms.forward_holomorphicAt F i
    (z.point.1.val, coordinate (A := A) i z) z.point.1.property (region_norm i hz)
  apply BeltramiMarkedReferenceMorphisms.holomorphicAt_of_realization A qX (homeomorph F) z
  · exact (homeomorph F).continuous.continuousAt
  · exact ambientParameter_holomorphic A qX z
  · apply (hg.comp z hinput).congr_of_eventuallyEq
    filter_upwards [(chartSource_open i).mem_nhds hz.1] with w hw
    exact forward_realization F i w hw

theorem image_conditions (i : Fin m) {z : TotalSpace A qX} (hz : z ∈ region (A := A) i) :
    homeomorph F z ∈ chartSource (A := A) i ∧
      ‖coordinate (A := A) i (homeomorph F z) - z.point.1.val.2 i‖ < 1 := by
  let p := ComplexBeltramiMarkParameters.productHomeomorph A z.point.1
  let D := F.disks p.1 i
  let x : NativeBeltramiSurface.Surface qX p.1.val := ⟨z.point.2⟩
  have hx : x ∈ PointTransportUniform.innerDisk D := ⟨hz.1, hz.2⟩
  have hsup := DisjointPointTransport.support_mem_nhds D hx.1
    (lt_trans (PointTransportUniform.innerDisk_norm D hx) (by norm_num))
  have hres := F.disk_restriction p.1 i p.2 x (mem_of_mem_nhds hsup)
  have hsrc : F.nativeMap p x ∈ D.chart.source := by
    rw [hres]
    exact PointTransportUniform.transport_source D (p.2 i) hx
  have hcoord : D.chart (F.nativeMap p x) = D.chart x + (p.2 i).val := by
    rw [hres]
    exact PointTransportUniform.transport_coordinate D (p.2 i) hx
  refine ⟨hsrc, ?_⟩
  change ‖D.chart (F.nativeMap p x) - (p.2 i).val‖ < 1
  rw [hcoord, add_sub_cancel_right]
  exact PointTransportUniform.innerDisk_norm D hx

theorem inverse_holomorphicAt (i : Fin m) {z : TotalSpace A qX} (hz : z ∈ region (A := A) i) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (homeomorph F).symm (homeomorph F z) := by
  let w := homeomorph F z
  have hw := image_conditions F i hz
  have hinput := (ambientParameter_holomorphic A qX w).prodMk_space (coordinate_holomorphicAt i hw.1)
  have hg := UniformBeltramiTransportGerms.inverse_holomorphicAt F i
    (w.point.1.val, coordinate (A := A) i w) w.point.1.property hw.2
  apply BeltramiMarkedReferenceMorphisms.holomorphicAt_of_realization A qX (homeomorph F).symm w
  · exact (homeomorph F).symm.continuous.continuousAt
  · exact ambientParameter_holomorphic A qX w
  · apply (hg.comp w hinput).congr_of_eventuallyEq
    filter_upwards [(chartSource_open i).mem_nhds hw.1] with v hv
    exact inverse_realization F i v hv

end VeechDichotomy.BeltramiMarkedTransportRegularity
