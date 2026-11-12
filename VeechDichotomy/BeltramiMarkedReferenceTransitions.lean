module

public import VeechDichotomy.BeltramiMarkedReferenceCharts

/-! Joint analytic compatibility of the constructed marked reference
charts. Each inverse is identified with an actual native total-family
chart inverse; the additional coordinates are retained by identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedReferenceTransitions

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData BeltramiMarkedReferenceCharts
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data qX b μ₀)
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (qY : Differential Y)

theorem inverse_realization_holomorphic (y : Y) {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ}
    (hp : p ∈ (chart A qY y).target) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (fun z => realization A qY ((chart A qY y).symm z)) p := by
  let c := NativeBeltramiTotalSpace.chart qY ⟨(μ₀, y)⟩
  have hsrc : realization A qY ((chart A qY y).symm p) ∈ c.source :=
    (NativeBeltramiCharts.chart_source qY y _).mpr
      ((chart_source A qY y _).mp ((chart A qY y).map_target hp))
  have hvalue : c (realization A qY ((chart A qY y).symm p)) = (p.1.1, p.2) := by
    rw [native_chart_value, (chart A qY y).right_inv hp]
  have ht : (p.1.1, p.2) ∈ c.target := hvalue ▸ c.map_source hsrc
  have hInv : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω c.symm (p.1.1, p.2) :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, y)⟩ : NativeBeltramiTotalSpace.TotalSpace qY)) ht
  have hinput : ContDiff ℂ ω (fun z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ => (z.1.1, z.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  apply (hInv.comp p (hinput.contMDiff p)).congr_of_eventuallyEq
  filter_upwards [(chart A qY y).open_target.mem_nhds hp] with z hz
  exact realization_inverse A qY y hz

theorem transition_holomorphic (i j : Y) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    (hp : p ∈ ((chart A qY i).symm.trans (chart A qY j)).source) :
    ContDiffAt ℂ ω ((chart A qY i).symm.trans (chart A qY j)) p := by
  let c := NativeBeltramiTotalSpace.chart qY ⟨(μ₀, j)⟩
  have hout : realization A qY ((chart A qY i).symm p) ∈ c.source :=
    (NativeBeltramiCharts.chart_source qY j _).mpr ((chart_source A qY j _).mp hp.2)
  have hchart : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω c
      (realization A qY ((chart A qY i).symm p)) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, j)⟩ : NativeBeltramiTotalSpace.TotalSpace qY)) hout
  have hcomp := hchart.comp p (inverse_realization_holomorphic A qY i hp.1)
  have hprod : ContDiffAt ℂ ω (fun z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ =>
      (z.1, (c (realization A qY ((chart A qY i).symm z))).2)) p :=
    contDiffAt_fst.prodMk hcomp.contDiffAt.snd
  apply hprod.congr_of_eventuallyEq
  filter_upwards [(chart A qY i).open_target.mem_nhds hp.1] with z hz
  refine Prod.ext ?_ ?_
  · exact inverse_parameter A qY i hz
  · rfl

theorem transition_holomorphicOn (i j : Y) :
    ContDiffOn ℂ ω ((chart A qY i).symm.trans (chart A qY j))
      ((chart A qY i).symm.trans (chart A qY j)).source :=
  fun p hp => (transition_holomorphic A qY i j p hp).contDiffWithinAt

end VeechDichotomy.BeltramiMarkedReferenceTransitions
