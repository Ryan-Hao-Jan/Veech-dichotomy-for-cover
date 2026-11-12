module

public import VeechDichotomy.BeltramiMarkedFixedSlices
public import VeechDichotomy.BeltramiMarkedFiberMap
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual joint covering-coordinate expressions in FIXED source and
base total charts. Their domain is open and their vertical derivative
is jointly analytic, including at differential zeros and ramification. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedCoverCoordinates

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

def center (s : ComplexBeltramiMarkParameters.Parameters A × Y) : BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch :=
  (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).symm s

def sourceChart (s : ComplexBeltramiMarkParameters.Parameters A × Y) :
    OpenPartialHomeomorph (BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch)
      (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :=
  HolomorphicCoverRelocationSpace.chart (BeltramiMarkedRelocationData.data π F hBranch) (center π F hBranch s)

def targetPoint (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : X :=
  (BeltramiMarkedCoverTotalSpace.map π F hBranch ((sourceChart π F hBranch s).symm p)).point.2

def domain (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) :
    Set (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :=
  (sourceChart π F hBranch s).target ∩ targetPoint π F hBranch s ⁻¹' (NativePowerCharts.chosen qX j).chart.source

theorem domain_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) : IsOpen (domain π F hBranch s j) := by
  have htarget : Continuous (fun x : BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch =>
      (BeltramiMarkedCoverTotalSpace.map π F hBranch x).point.2) :=
    continuous_snd.comp ((BeltramiMarkedReferenceSpace.toProduct A qX).continuous.comp
      (BeltramiMarkedCoverTotalSpace.holomorphic_map π F hBranch).continuous)
  exact (htarget.comp_continuousOn (sourceChart π F hBranch s).symm.continuousOn).isOpen_inter_preimage
    (sourceChart π F hBranch s).open_target (NativePowerCharts.chosen qX j).chart.open_source

def expression (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : ℂ :=
  (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩ (BeltramiMarkedReferenceSpace.realization A qX
    (BeltramiMarkedCoverTotalSpace.map π F hBranch ((sourceChart π F hBranch s).symm p)))).2

theorem expression_holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hp : p ∈ domain π F hBranch s j) :
    ContDiffAt ℂ ω (expression π F hBranch s j) p := by
  have hi : ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (sourceChart π F hBranch s).symm p :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (center π F hBranch s)) hp.1
  have hmap := (BeltramiMarkedCoverTotalSpace.holomorphic_map π F hBranch _).comp p hi
  have hr := (BeltramiMarkedReferenceSpace.realization_holomorphic A qX _).comp p hmap
  have hc : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩)
      (BeltramiMarkedReferenceSpace.realization A qX
        (BeltramiMarkedCoverTotalSpace.map π F hBranch ((sourceChart π F hBranch s).symm p))) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, j)⟩ : NativeBeltramiTotalSpace.TotalSpace qX))
      ((NativeBeltramiCharts.chart_source qX j _).mpr hp.2)
  have hcomp := hc.comp p hr
  exact ((contDiff_snd.contMDiff _).comp p hcomp).contDiffAt

def verticalDerivative (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : ℂ :=
  fderiv ℂ (expression π F hBranch s j) p (0, 1)

theorem verticalDerivative_holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hp : p ∈ domain π F hBranch s j) :
    ContDiffAt ℂ ω (verticalDerivative π F hBranch s j) p := by
  have hd : ContDiffAt ℂ ω (fderiv ℂ (expression π F hBranch s j)) p :=
    (expression_holomorphicAt π F hBranch s j hp).fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)).contDiff.contDiffAt.comp p hd

theorem source_inverse_value (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (a : ComplexBeltramiMarkParameters.Parameters A) {z : ℂ}
    (hz : z ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).target) :
    (sourceChart π F hBranch s).symm (a.val, z) = BeltramiMarkedFiberSurface.inclusion π F hBranch a
      ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z) := by
  apply (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).injective
  exact BeltramiMarkedFixedSlices.inverse_value π F hBranch s a hz

def fiberExpression (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) (z : ℂ) : ℂ :=
  NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨j⟩
    (BeltramiMarkedFiberMap.map π F hBranch a ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z))

theorem expression_fiber_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {z : ℂ}
    (hz : z ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).target) :
    expression π F hBranch s j (a.val, z) = fiberExpression π F hBranch s j a z := by
  rw [expression, source_inverse_value π F hBranch s a hz, BeltramiMarkedFiberMap.total_map]
  rfl

theorem fiber_domain (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) (z : ℂ) :
    (a.val, z) ∈ domain π F hBranch s j ↔
      z ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).target ∧
      BeltramiMarkedFiberMap.map π F hBranch a ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z) ∈
        (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨j⟩).source := by
  constructor
  · intro hp
    have hz : z ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).target := hp.1
    refine ⟨hz, ?_⟩
    have hbase := hp.2
    change (BeltramiMarkedCoverTotalSpace.map π F hBranch ((sourceChart π F hBranch s).symm (a.val, z))).point.2 ∈
      (NativePowerCharts.chosen qX j).chart.source at hbase
    rw [source_inverse_value π F hBranch s a hz] at hbase
    exact hbase
  · rintro ⟨hz, hbase⟩
    refine ⟨hz, ?_⟩
    change (BeltramiMarkedCoverTotalSpace.map π F hBranch ((sourceChart π F hBranch s).symm (a.val, z))).point.2 ∈
      (NativePowerCharts.chosen qX j).chart.source
    rw [source_inverse_value π F hBranch s a hz]
    exact hbase

theorem verticalDerivative_eq_deriv (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {z : ℂ} (hp : (a.val, z) ∈ domain π F hBranch s j) :
    verticalDerivative π F hBranch s j (a.val, z) = deriv (fiberExpression π F hBranch s j a) z := by
  have hz := ((fiber_domain π F hBranch s j a z).mp hp).1
  have hG := ((expression_holomorphicAt π F hBranch s j hp).differentiableAt (by decide)).hasFDerivAt
  have hslice : HasDerivAt (fun w : ℂ => (a.val, w)) (0, 1) z :=
    (hasDerivAt_const z a.val).prodMk (hasDerivAt_id z)
  have hline := hG.comp_hasDerivAt z hslice
  have heq : fiberExpression π F hBranch s j a =ᶠ[𝓝 z] fun w => expression π F hBranch s j (a.val, w) := by
    filter_upwards [(BeltramiMarkedFixedSlices.chart π F hBranch s a).open_target.mem_nhds hz] with w hw
    exact (expression_fiber_value π F hBranch s j a hw).symm
  exact (hline.congr_of_eventuallyEq heq).deriv.symm

end VeechDichotomy.BeltramiMarkedCoverCoordinates
