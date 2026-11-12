module

public import VeechDichotomy.NativeBeltramiCoverVerticalDerivative
public import VeechDichotomy.RelocatedCoverCharts

/-! Actual jointly holomorphic local inverses of the total covering
map off ramification. The topological local inverse is the original local
cover inverse times the parameter; analyticity is derived from its actual
triangular derivative, rather than supplied as inverse data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiLocalCoverInverse

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCoverCoordinates
open BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} (π : Cover ωX ωY)

def localMap (y : RelocatedCoverCharts.RegularPoint π) :
    OpenPartialHomeomorph (NativeBeltramiTotalSpace.TotalSpace ωY) (NativeBeltramiTotalSpace.TotalSpace ωX) :=
  ((NativeBeltramiTotalSpace.toProduct ωY).transOpenPartialHomeomorph
    ((OpenPartialHomeomorph.refl Parameter).prod (RelocatedCoverCharts.oldLocalMap π y))).transHomeomorph
      (NativeBeltramiTotalSpace.toProduct ωX).symm

theorem source_iff (y : RelocatedCoverCharts.RegularPoint π) (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    z ∈ (localMap π y).source ↔ z.point.2 ∈ (RelocatedCoverCharts.oldLocalMap π y).source := by
  change (z.point.1 ∈ univ ∧ z.point.2 ∈ (RelocatedCoverCharts.oldLocalMap π y).source) ↔ _
  simp only [mem_univ, true_and]

theorem center_source (y : RelocatedCoverCharts.RegularPoint π) (μ : Parameter) :
    (⟨(μ, y.val)⟩ : NativeBeltramiTotalSpace.TotalSpace ωY) ∈ (localMap π y).source :=
  (source_iff π y _).mpr (RelocatedCoverCharts.localMap_center π (Homeomorph.refl X) y)

theorem localMap_apply (y : RelocatedCoverCharts.RegularPoint π) (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    localMap π y z = NativeBeltramiCoverTotalMap.map π z := by
  apply (NativeBeltramiTotalSpace.toProduct ωX).injective
  refine Prod.ext rfl ?_
  exact RelocatedCoverCharts.localMap_apply π (Homeomorph.refl X) y z.point.2

theorem holomorphic_localMap (y : RelocatedCoverCharts.RegularPoint π) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (localMap π y) := by
  intro z
  apply (NativeBeltramiCoverJoint.holomorphic_map π z).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (localMap_apply π y)

theorem noncritical (y : RelocatedCoverCharts.RegularPoint π) {z : NativeBeltramiTotalSpace.TotalSpace ωY}
    (hz : z ∈ (localMap π y).source) : z.point.2 ∉ criticalSet π :=
  RelocatedCoverCharts.localMap_source_noncritical π (Homeomorph.refl X) y ((source_iff π y z).mp hz)

def coordinate (y : RelocatedCoverCharts.RegularPoint π) (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  ((NativeBeltramiTotalSpace.chart ωY z).symm.trans (localMap π y)).trans
    (NativeBeltramiTotalSpace.chart ωX (NativeBeltramiCoverTotalMap.map π z))

theorem coordinate_function (y : RelocatedCoverCharts.RegularPoint π) (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    (coordinate π y z : (ℂ × ℂ) → (ℂ × ℂ)) = coordinateMap π z.point.2 := by
  funext p
  change NativeBeltramiTotalSpace.chart ωX (NativeBeltramiCoverTotalMap.map π z)
    (localMap π y ((NativeBeltramiTotalSpace.chart ωY z).symm p)) = _
  rw [localMap_apply]
  rfl

theorem chart_center_value (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    NativeBeltramiTotalSpace.chart ωY z z = (z.point.1.val, 0) :=
  source_center_value (ωY := ωY) z.point.2 z.point.1

theorem coordinate_source (y : RelocatedCoverCharts.RegularPoint π) {z : NativeBeltramiTotalSpace.TotalSpace ωY}
    (hz : z ∈ (localMap π y).source) : (z.point.1.val, 0) ∈ (coordinate π y z).source := by
  let c := NativeBeltramiTotalSpace.chart ωY z
  have hc : z ∈ c.source := NativeBeltramiTotalSpace.chart_center ωY z
  have hInv : c.symm (z.point.1.val, 0) = z := by rw [← chart_center_value z]; exact c.left_inv hc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← chart_center_value z]
    exact c.map_source hc
  · change c.symm (z.point.1.val, 0) ∈ (localMap π y).source
    rwa [hInv]
  · change localMap π y (c.symm (z.point.1.val, 0)) ∈
      (NativeBeltramiTotalSpace.chart ωX (NativeBeltramiCoverTotalMap.map π z)).source
    rw [hInv, localMap_apply]
    exact NativeBeltramiTotalSpace.chart_center ωX _

theorem coordinate_center (y : RelocatedCoverCharts.RegularPoint π) (z : NativeBeltramiTotalSpace.TotalSpace ωY) :
    coordinate π y z (z.point.1.val, 0) = (z.point.1.val, 0) := by
  rw [coordinate_function]
  change NativeBeltramiCharts.chart ωX (π.map z.point.2)
    (NativeBeltramiCoverTotalMap.underlying π ((NativeBeltramiCharts.chart ωY z.point.2).symm (z.point.1.val, 0))) = _
  rw [source_inverse_center]
  exact source_center_value (ωY := ωX) (π.map z.point.2) z.point.1

theorem coordinate_inverse_holomorphic (y : RelocatedCoverCharts.RegularPoint π)
    {z : NativeBeltramiTotalSpace.TotalSpace ωY} (hz : z ∈ (localMap π y).source) :
    ContDiffAt ℂ ω (coordinate π y z).symm (z.point.1.val, 0) := by
  have hsrc := coordinate_source π y hz
  have hforward : ContDiffAt ℂ ω (coordinate π y z) (z.point.1.val, 0) := by
    rw [coordinate_function]
    exact NativeBeltramiCoverJoint.coordinate_holomorphic π z.point.2 z.point.1
  have hfirst : ∀ᶠ p in 𝓝 (z.point.1.val, 0), (coordinate π y z p).1 = p.1 := by
    filter_upwards [(NativeBeltramiCharts.chart ωY z.point.2).open_target.mem_nhds
      (domain_center π z.point.2 z.point.1).1] with p hp
    rw [coordinate_function]
    exact coordinate_first π z.point.2 hp
  have hvertical : (fderiv ℂ (coordinate π y z) (z.point.1.val, 0) (0, 1)).2 ≠ 0 := by
    rw [coordinate_function]
    exact NativeBeltramiCoverVerticalDerivative.vertical_ne_zero π z.point.2 (noncritical π y hz) z.point.1
  have h := TriangularHolomorphicInverse.contDiffAt_symm (coordinate π y z) hsrc hforward hfirst hvertical
  rwa [coordinate_center] at h

theorem inverse_holomorphicAt (y : RelocatedCoverCharts.RegularPoint π)
    {z : NativeBeltramiTotalSpace.TotalSpace ωY} (hz : z ∈ (localMap π y).source) :
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (localMap π y).symm (NativeBeltramiCoverTotalMap.map π z) := by
  let c := NativeBeltramiTotalSpace.chart ωY z
  let d := NativeBeltramiTotalSpace.chart ωX (NativeBeltramiCoverTotalMap.map π z)
  let e := localMap π y
  have htarget : NativeBeltramiCoverTotalMap.map π z ∈ e.target := by
    rw [← localMap_apply π y z]
    exact e.map_source hz
  have heInv : e.symm (NativeBeltramiCoverTotalMap.map π z) = z := by
    rw [← localMap_apply π y z]
    exact e.left_inv hz
  have hc : z ∈ c.source := NativeBeltramiTotalSpace.chart_center ωY z
  have hd : NativeBeltramiCoverTotalMap.map π z ∈ d.source := NativeBeltramiTotalSpace.chart_center ωX _
  have hdvalue : d (NativeBeltramiCoverTotalMap.map π z) = (z.point.1.val, 0) :=
    source_center_value (ωY := ωX) (π.map z.point.2) z.point.1
  have hCInv : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (coordinate π y z).symm
      (d (NativeBeltramiCoverTotalMap.map π z)) := by
    rw [hdvalue]
    exact (coordinate_inverse_holomorphic π y hz).contMDiffAt
  have hcenter : (coordinate π y z).symm (d (NativeBeltramiCoverTotalMap.map π z)) = c z := by
    rw [hdvalue, chart_center_value z]
    simpa only [coordinate_center] using (coordinate π y z).left_inv (coordinate_source π y hz)
  have hcInv : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω c.symm
      ((coordinate π y z).symm (d (NativeBeltramiCoverTotalMap.map π z))) := by
    rw [hcenter]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z) (c.map_source hc)
  have hdH : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω d (NativeBeltramiCoverTotalMap.map π z) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (NativeBeltramiCoverTotalMap.map π z)) hd
  have hcomp := hcInv.comp (NativeBeltramiCoverTotalMap.map π z)
    (hCInv.comp (NativeBeltramiCoverTotalMap.map π z) hdH)
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ x in 𝓝 (NativeBeltramiCoverTotalMap.map π z), e.symm x ∈ c.source := by
    have hi := (e.symm.continuousAt htarget).tendsto
    rw [heInv] at hi
    exact hi (c.open_source.mem_nhds hc)
  filter_upwards [d.open_source.mem_nhds hd, hnear] with x hxD hxC
  change e.symm x = c.symm (c (e.symm (d.symm (d x))))
  rw [d.left_inv hxD, c.left_inv hxC]

theorem inverse_holomorphicOn (y : RelocatedCoverCharts.RegularPoint π) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (localMap π y).symm (localMap π y).target := by
  intro x hx
  have h := inverse_holomorphicAt π y ((localMap π y).map_target hx)
  have hvalue : NativeBeltramiCoverTotalMap.map π ((localMap π y).symm x) = x :=
    (localMap_apply π y _).symm.trans ((localMap π y).right_inv hx)
  rw [hvalue] at h
  exact h.contMDiffWithinAt

end VeechDichotomy.NativeBeltramiLocalCoverInverse
