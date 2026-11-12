module

public import VeechDichotomy.ParameterSliceChart
public import VeechDichotomy.BeltramiMarkedCoverTotalSpace

/-! Actual one-dimensional fiber charts obtained by slicing the
constructed source total charts. Their transition analyticity is the
restriction of the already checked joint transition, including at zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def totalChart (a : ComplexBeltramiMarkParameters.Parameters A) (y : Y) :
    OpenPartialHomeomorph (ComplexBeltramiMarkParameters.Parameters A × Y)
      (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :=
  (BeltramiMarkedReferenceSpace.toProduct A qY).symm.transOpenPartialHomeomorph
    (HolomorphicCoverRelocationTransitions.rawChart (BeltramiMarkedRelocationData.data π F hBranch) ⟨(a, y)⟩)

theorem total_parameter (a : ComplexBeltramiMarkParameters.Parameters A) (y : Y)
    (p : ComplexBeltramiMarkParameters.Parameters A × Y) :
    (totalChart π F hBranch a y p).1 = p.1.val :=
  BeltramiMarkedCoverTotalSpace.rawChart_parameter π F hBranch ⟨(a, y)⟩ ⟨p⟩

def chart (a : ComplexBeltramiMarkParameters.Parameters A) (y : Y) : OpenPartialHomeomorph Y ℂ :=
  ParameterSliceChart.chart Subtype.val Subtype.val_injective (totalChart π F hBranch a y)
    (fun p _ => total_parameter π F hBranch a y p) a

theorem chart_apply (a : ComplexBeltramiMarkParameters.Parameters A) (i y : Y) :
    chart π F hBranch a i y = (totalChart π F hBranch a i (a, y)).2 := rfl

theorem chart_symm_apply (a : ComplexBeltramiMarkParameters.Parameters A) (i : Y) (z : ℂ) :
    (chart π F hBranch a i).symm z = ((totalChart π F hBranch a i).symm (a.val, z)).2 := rfl

theorem chart_source (a : ComplexBeltramiMarkParameters.Parameters A) (i y : Y) :
    y ∈ (chart π F hBranch a i).source ↔ (a, y) ∈ (totalChart π F hBranch a i).source := Iff.rfl

theorem chart_target (a : ComplexBeltramiMarkParameters.Parameters A) (i : Y) (z : ℂ) :
    z ∈ (chart π F hBranch a i).target ↔ (a.val, z) ∈ (totalChart π F hBranch a i).target := Iff.rfl

theorem chart_center (a : ComplexBeltramiMarkParameters.Parameters A) (y : Y) :
    y ∈ (chart π F hBranch a y).source :=
  HolomorphicCoverRelocationTransitions.rawChart_center (BeltramiMarkedRelocationData.data π F hBranch) ⟨(a, y)⟩

theorem inverse_value (a : ComplexBeltramiMarkParameters.Parameters A) (i : Y) {z : ℂ}
    (hz : z ∈ (chart π F hBranch a i).target) :
    (totalChart π F hBranch a i).symm (a.val, z) = (a, (chart π F hBranch a i).symm z) :=
  ParameterSliceChart.inverse_pair Subtype.val Subtype.val_injective (totalChart π F hBranch a i)
    (fun p _ => total_parameter π F hBranch a i p) a hz

theorem total_value (a : ComplexBeltramiMarkParameters.Parameters A) (i y : Y) :
    totalChart π F hBranch a i (a, y) = (a.val, chart π F hBranch a i y) :=
  Prod.ext (total_parameter π F hBranch a i (a, y)) rfl

theorem total_transition_source (a : ComplexBeltramiMarkParameters.Parameters A) (i j : Y) {z : ℂ}
    (hz : z ∈ ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)).source) :
    (a.val, z) ∈ ((totalChart π F hBranch a i).symm.trans (totalChart π F hBranch a j)).source := by
  refine ⟨hz.1, ?_⟩
  change (totalChart π F hBranch a i).symm (a.val, z) ∈ (totalChart π F hBranch a j).source
  rw [inverse_value π F hBranch a i hz.1]
  exact hz.2

theorem transition_value (a : ComplexBeltramiMarkParameters.Parameters A) (i j : Y) {z : ℂ}
    (hz : z ∈ (chart π F hBranch a i).target) :
    (((totalChart π F hBranch a i).symm.trans (totalChart π F hBranch a j)) (a.val, z)).2 =
      ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)) z := by
  rw [OpenPartialHomeomorph.trans_apply, inverse_value π F hBranch a i hz]
  rfl

theorem transition_holomorphic (a : ComplexBeltramiMarkParameters.Parameters A) (i j : Y) (z : ℂ)
    (hz : z ∈ ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)).source) :
    ContDiffAt ℂ ω ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)) z := by
  have ht := total_transition_source π F hBranch a i j hz
  have htotal : ContDiffAt ℂ ω ((totalChart π F hBranch a i).symm.trans (totalChart π F hBranch a j)) (a.val, z) :=
    HolomorphicCoverRelocationTransitions.rawChart_transition (BeltramiMarkedRelocationData.data π F hBranch)
      ⟨(a, i)⟩ ⟨(a, j)⟩ ht
  have hslice : ContDiffAt ℂ ω (fun w : ℂ => (a.val, w)) z := contDiffAt_const.prodMk contDiffAt_id
  have hcomp := contDiffAt_snd.comp z (htotal.comp z hslice)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(chart π F hBranch a i).open_target.mem_nhds hz.1] with w hw
  exact (transition_value π F hBranch a i j hw).symm

theorem transition_holomorphicOn (a : ComplexBeltramiMarkParameters.Parameters A) (i j : Y) :
    ContDiffOn ℂ ω ((chart π F hBranch a i).symm.trans (chart π F hBranch a j))
      ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)).source :=
  fun z hz => (transition_holomorphic π F hBranch a i j z hz).contDiffWithinAt

end VeechDichotomy.BeltramiMarkedFiberCharts
