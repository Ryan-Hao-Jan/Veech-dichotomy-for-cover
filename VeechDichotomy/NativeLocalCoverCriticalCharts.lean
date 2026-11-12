module

public import VeechDichotomy.UniformCriticalNeighborhood
public import VeechDichotomy.RelocatedCoverLocalIdentity
public import VeechDichotomy.ParameterizedCoverChart

/-! Parameter-independent old holomorphic critical charts are genuine
holomorphic charts for every actual relocated source. This verifies local
complex-structure agreement, not only a topological chart formula. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverCriticalCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeLocalCoverFamily
open Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) (b : Fin m → X) (hBranch : range b = branchValues π)
  (S : NativeUniformMarkTransport.Transport b)

theorem toOriginal_mdifferentiableAt (u : S.marks.neighborhood)
    {i : Source π b hBranch S.marks u} (hi : i.point ∈ UniformCriticalNeighborhood.region π S) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toOriginal π b hBranch S.marks u) i :=
  RelocatedCoverLocalIdentity.toOriginal_mdifferentiableAt π (S.marks.transport u) _ _
    (UniformCriticalNeighborhood.region_open π S) (fun _ hz => UniformCriticalNeighborhood.analytic π S u hz) hi

theorem fromOriginal_mdifferentiableAt (u : S.marks.neighborhood) {y : Y}
    (hy : y ∈ UniformCriticalNeighborhood.region π S) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toOriginal π b hBranch S.marks u).symm y :=
  RelocatedCoverLocalIdentity.fromOriginal_mdifferentiableAt π (S.marks.transport u) _ _
    (UniformCriticalNeighborhood.region_open π S) (fun _ hz => UniformCriticalNeighborhood.analytic π S u hz)
    (i := (toOriginal π b hBranch S.marks u).symm y) hy

def chart (u : S.marks.neighborhood) (y : Y) : OpenPartialHomeomorph (Source π b hBranch S.marks u) ℂ :=
  (toOriginal π b hBranch S.marks u).transOpenPartialHomeomorph (UniformCriticalNeighborhood.chart π S y)

theorem chart_mdifferentiable (u : S.marks.neighborhood) (y : Y) :
    (chart π b hBranch S u y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · intro i hi
    have hiOld : i.point ∈ (UniformCriticalNeighborhood.chart π S y).source := hi
    have hiRegion := interior_subset hiOld.2
    exact (((UniformCriticalNeighborhood.chart_mdifferentiable π S y).mdifferentiableAt hiOld).comp i
      (toOriginal_mdifferentiableAt π b hBranch S u hiRegion)).mdifferentiableWithinAt
  · intro z hz
    have hOld := (UniformCriticalNeighborhood.chart_mdifferentiable π S y).mdifferentiableAt_symm hz
    have hyOld := (UniformCriticalNeighborhood.chart π S y).map_target hz
    exact ((fromOriginal_mdifferentiableAt π b hBranch S u (interior_subset hyOld.2)).comp z hOld).mdifferentiableWithinAt

theorem critical_chart_center (u : S.marks.neighborhood) {y : Y} (hy : y ∈ criticalSet π) :
    (toOriginal π b hBranch S.marks u).symm y ∈ (chart π b hBranch S u y).source :=
  UniformCriticalNeighborhood.critical_chart_center π S hBranch hy

def totalChart (y : Y) : OpenPartialHomeomorph (S.marks.neighborhood × Y) (S.marks.neighborhood × ℂ) :=
  (OpenPartialHomeomorph.refl S.marks.neighborhood).prod (UniformCriticalNeighborhood.chart π S y)

theorem total_chart_value (u : S.marks.neighborhood) (y z : Y) :
    chart π b hBranch S u y ((toOriginal π b hBranch S.marks u).symm z) =
      (totalChart π b S y (u, z)).2 := rfl

end VeechDichotomy.NativeLocalCoverCriticalCharts
