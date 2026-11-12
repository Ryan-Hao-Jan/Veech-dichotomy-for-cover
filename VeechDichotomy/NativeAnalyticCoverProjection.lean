module

public import VeechDichotomy.NativeAnalyticCoverFiberCharts

/-! The actual covering projections assemble into a holomorphic map from
the constructed complex total space to the fixed native base curve. This
includes all critical points and is joint in parameter and source. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverProjection

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters NativeAnalyticCoverCharts NativeAnalyticCoverTransitions
open NativeAnalyticCoverTotalSpace HolomorphicCurveGerms PointTransportUniform
open AnalyticTransportCoordinates Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π)

def map (p : TotalSpace π A hBranch) : X := transported A p.point.1 (π.map p.point.2)

theorem continuous_map : Continuous (map π A hBranch) :=
  (NativeMovingCoverMap.continuous_family π (transported A) (transported_continuous A)).comp
    (toProduct π A hBranch).continuous

theorem fiber_cover_map (a : Parameters m) (z : NativeAnalyticCoverFiberCharts.Source π b hBranch A a) :
    (NativeLocalCoverFamily.cover π b hBranch A.marks (A.tuple a)).map z =
      map π A hBranch (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a z) :=
  congrArg (fun H : X ≃ₜ X => H (π.map z.point)) (A.transport_in_coordinates a)

theorem chart_critical_value {i : TotalSpace π A hBranch} (hi : i.point.2 ∈ criticalSet π)
    (p : TotalSpace π A hBranch) : NativeAnalyticCoverTotalSpace.chart π A hBranch i p =
      (p.point.1.val, UniformCriticalNeighborhood.chart π A.uniform i.point.2 p.point.2) := by
  change rawChart π A i.point p.point = _
  rw [rawChart, dite_eq_left hi]
  rfl

theorem chart_regular_value {i : TotalSpace π A hBranch} (hi : i.point.2 ∉ criticalSet π)
    (p : TotalSpace π A hBranch) : NativeAnalyticCoverTotalSpace.chart π A hBranch i p =
      (p.point.1.val, chartAt ℂ (map π A hBranch i) (map π A hBranch p)) := by
  change rawChart π A i.point p.point = _
  rw [rawChart, dite_eq_right hi, regular_apply]
  rfl

theorem holomorphic_map : ContMDiff 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) ω (map π A hBranch) := by
  intro i
  let C := NativeAnalyticCoverTotalSpace.chart π A hBranch i
  have hC : ContMDiffAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m × ℂ) ω C i :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Space m × ℂ)) (x := i)).contMDiffAt
      (C.open_source.mem_nhds (NativeAnalyticCoverTotalSpace.chart_center π A hBranch i))
  by_cases hi : i.point.2 ∈ criticalSet π
  · let c := UniformCriticalNeighborhood.chart π A.uniform i.point.2
    have hs : i.point.2 ∈ c.source := UniformCriticalNeighborhood.critical_chart_center π A.uniform hBranch hi
    have hct : c i.point.2 ∈ c.target := c.map_source hs
    have hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (π.map ∘ c.symm) (c i.point.2) :=
      (π.holomorphic (c.symm (c i.point.2))).comp _
        (chart_contMDiffAt_symm c (UniformCriticalNeighborhood.chart_mdifferentiable π A.uniform i.point.2) hct)
    have hb : π.map i.point.2 ∈ range b := by rw [hBranch]; exact ⟨i.point.2, hi, rfl⟩
    obtain ⟨k, hk⟩ := hb
    have hinner : π.map (c.symm (c i.point.2)) ∈ innerDisk (A.disks k) := by
      rw [c.left_inv hs, ← hk, ← A.centers k]
      exact center_mem_innerDisk (A.disks k)
    have hF := AnalyticTransportSmoothCompositions.forward_contMDiffAt A.disks A.combined A.restriction
      k (A.holomorphic k) (π.map ∘ c.symm) (i.point.1.val, c i.point.2) i.point.1.property hinner hf
    have hcoord : (i.point.1.val, c i.point.2) = C i := (chart_critical_value π A hBranch hi i).symm
    rw [hcoord] at hF
    apply (hF.comp i hC).congr_of_eventuallyEq
    filter_upwards [C.open_source.mem_nhds (NativeAnalyticCoverTotalSpace.chart_center π A hBranch i)] with z hz
    have hzRaw : z.point ∈ (rawChart π A i.point).source := hz
    rw [rawChart, dite_eq_left hi] at hzRaw
    have hzOld : z.point.2 ∈ c.source := hzRaw.2
    change map π A hBranch z = ambientTransport A.combined (C z).1 (π.map (c.symm (C z).2))
    have hval : C z = (z.point.1.val, c z.point.2) := chart_critical_value π A hBranch hi z
    rw [hval, c.left_inv hzOld]
    exact congrArg (fun H : X ≃ₜ X => H (π.map z.point.2))
      ((A.ambient_in_coordinates z.point.1).trans (A.transport_in_coordinates z.point.1)).symm
  · let c := chartAt ℂ (map π A hBranch i)
    have ht : (C i).2 ∈ c.target := by
      rw [chart_regular_value π A hBranch hi i]
      exact c.map_source (mem_chart_source ℂ (map π A hBranch i))
    have hInv := chart_contMDiffAt_symm c (mdifferentiable_chart (map π A hBranch i)) ht
    have hflat : ContMDiff 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) ω (Prod.snd : Space m × ℂ → ℂ) := contDiff_snd.contMDiff
    have hsnd := (hflat (C i)).comp i hC
    apply (hInv.comp i hsnd).congr_of_eventuallyEq
    filter_upwards [C.open_source.mem_nhds (NativeAnalyticCoverTotalSpace.chart_center π A hBranch i)] with z hz
    have hzRaw : z.point ∈ (rawChart π A i.point).source := hz
    rw [rawChart, dite_eq_right hi] at hzRaw
    have hzTarget : map π A hBranch z ∈ c.source := ((regular_source π A ⟨i.point.2, hi⟩ c z.point).mp hzRaw).2
    change map π A hBranch z = c.symm (C z).2
    rw [chart_regular_value π A hBranch hi z]
    exact (c.left_inv hzTarget).symm

end VeechDichotomy.NativeAnalyticCoverProjection
