module

public import VeechDichotomy.NativeAnalyticCoverTotalSpace

/-! The complex vertical charts of the total family agree literally with
genuine biholomorphic charts on the previously constructed native covers.
The actual source of each cover is homeomorphic to the projection fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverFiberCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open NativeLocalCoverFamily ComplexDisplacementParameters NativeAnalyticCoverCharts
open NativeAnalyticCoverTransitions Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) (b : Fin m → X) (hBranch : range b = branchValues π) (A : Data b)

abbrev Source (a : Parameters m) := NativeLocalCoverFamily.Source π b hBranch A.marks (A.tuple a)

def chart (a : Parameters m) (y : Y) : OpenPartialHomeomorph (Source π b hBranch A a) ℂ := by
  classical
  exact if hy : y ∈ criticalSet π then NativeLocalCoverCriticalCharts.chart π b hBranch A.uniform (A.tuple a) y else
    NativeLocalCoverRegularCharts.chart π b hBranch A.marks (A.tuple a) ⟨y, hy⟩
      (chartAt ℂ (transported A a (π.map y)))

theorem chart_mdifferentiable (a : Parameters m) (y : Y) :
    (chart π b hBranch A a y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  by_cases hy : y ∈ criticalSet π
  · rw [chart, dite_eq_left hy]
    exact NativeLocalCoverCriticalCharts.chart_mdifferentiable π b hBranch A.uniform (A.tuple a) y
  · rw [chart, dite_eq_right hy]
    exact NativeLocalCoverRegularCharts.chart_mdifferentiable π b hBranch A.marks (A.tuple a) ⟨y, hy⟩ _
      (mdifferentiable_chart _)

theorem chart_value (a : Parameters m) (y : Y) (z : Source π b hBranch A a) :
    chart π b hBranch A a y z = (rawChart π A (a, y) (a, z.point)).2 := by
  by_cases hy : y ∈ criticalSet π
  · rw [chart, dite_eq_left hy, rawChart, dite_eq_left hy]
    rfl
  · rw [chart, dite_eq_right hy, rawChart, dite_eq_right hy, regular_apply]
    change chartAt ℂ (transported A a (π.map y))
      (RelocatedCoverCharts.localMap π (A.marks.transport (A.tuple a)) ⟨y, hy⟩ z.point) = _
    rw [RelocatedCoverCharts.localMap_apply]
    exact congrArg (fun H : X ≃ₜ X => chartAt ℂ (transported A a (π.map y)) (H (π.map z.point)))
      (A.transport_in_coordinates a)

theorem chart_source (a : Parameters m) (y : Y) (z : Source π b hBranch A a) :
    z ∈ (chart π b hBranch A a y).source ↔ (a, z.point) ∈ (rawChart π A (a, y)).source := by
  by_cases hy : y ∈ criticalSet π
  · rw [chart, dite_eq_left hy, rawChart, dite_eq_left hy]
    change z.point ∈ (UniformCriticalNeighborhood.chart π A.uniform y).source ↔
      (a ∈ univ ∧ z.point ∈ (UniformCriticalNeighborhood.chart π A.uniform y).source)
    simp only [mem_univ, true_and]
  · rw [chart, dite_eq_right hy, rawChart, dite_eq_right hy, regular_source]
    change (z.point ∈ (RelocatedCoverCharts.oldLocalMap π ⟨y, hy⟩).source ∧
      RelocatedCoverCharts.localMap π (A.marks.transport (A.tuple a)) ⟨y, hy⟩ z.point ∈
        (chartAt ℂ (transported A a (π.map y))).source) ↔ _
    rw [RelocatedCoverCharts.localMap_apply]
    have hval := congrArg (fun H : X ≃ₜ X => H (π.map z.point)) (A.transport_in_coordinates a)
    change (_ ∧ A.marks.transport (A.tuple a) (π.map z.point) ∈ _) ↔ _
    rw [hval]
    rfl

theorem chart_center (a : Parameters m) (z : Source π b hBranch A a) :
    z ∈ (chart π b hBranch A a z.point).source :=
  (chart_source π b hBranch A a z.point z).mpr (rawChart_center π A hBranch (a, z.point))

def fiberHomeomorph (a : Parameters m) : Source π b hBranch A a ≃ₜ
    (NativeAnalyticCoverTotalSpace.projection π A hBranch ⁻¹' {a}) where
  toFun z := ⟨⟨(a, z.point)⟩, rfl⟩
  invFun z := (toOriginal π b hBranch A.marks (A.tuple a)).symm z.val.point.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply (NativeAnalyticCoverTotalSpace.toProduct π A hBranch).injective
    exact Prod.ext z.property.symm rfl
  continuous_toFun := ((NativeAnalyticCoverTotalSpace.toProduct π A hBranch).symm.continuous.comp
    (continuous_const.prodMk (toOriginal π b hBranch A.marks (A.tuple a)).continuous)).subtype_mk _
  continuous_invFun := (toOriginal π b hBranch A.marks (A.tuple a)).symm.continuous.comp
    (continuous_snd.comp ((NativeAnalyticCoverTotalSpace.toProduct π A hBranch).continuous.comp continuous_subtype_val))

def inclusion (a : Parameters m) (z : Source π b hBranch A a) :
    NativeAnalyticCoverTotalSpace.TotalSpace π A hBranch := (fiberHomeomorph π b hBranch A a z).val

theorem continuous_inclusion (a : Parameters m) : Continuous (inclusion π b hBranch A a) :=
  continuous_subtype_val.comp (fiberHomeomorph π b hBranch A a).continuous

theorem holomorphic_inclusion (a : Parameters m) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Space m × ℂ) ω (inclusion π b hBranch A a) := by
  intro z
  rw [contMDiffAt_iff_target_of_mem_source
    (y := inclusion π b hBranch A a z) (mem_chart_source (Space m × ℂ) (inclusion π b hBranch A a z))]
  refine ⟨(continuous_inclusion π b hBranch A a).continuousAt, ?_⟩
  have heq : (extChartAt 𝓘(ℂ, Space m × ℂ) (inclusion π b hBranch A a z) ∘ inclusion π b hBranch A a) =
      fun w => (a.val, chart π b hBranch A a z.point w) := by
    funext w
    change rawChart π A (a, z.point) (a, w.point) = (a.val, chart π b hBranch A a z.point w)
    exact Prod.ext (rawChart_parameter π A (a, z.point) (a, w.point)) (chart_value π b hBranch A a z.point w).symm
  rw [heq]
  have hconst : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Space m) ω (fun _ : Source π b hBranch A a => a.val) z := contMDiffAt_const
  have hcurve : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chart π b hBranch A a z.point) z :=
    HolomorphicCurveGerms.chart_contMDiffAt _ (chart_mdifferentiable π b hBranch A a z.point)
      (chart_center π b hBranch A a z)
  exact hconst.prodMk_space hcurve

end VeechDichotomy.NativeAnalyticCoverFiberCharts
