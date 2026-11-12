module

public import VeechDichotomy.BeltramiMarkedShiftedClocks
public import VeechDichotomy.NativeShiftedRayOrbitCounts
public import VeechDichotomy.NativeCompleteOrbitShifts

/-! Source points may move along their actual complete native orbits by
a bounded ray-time shift. Their images are actual target vertical flow
points. Translated source windows still have exact common lengths and
finite limiting ratios to the reference clock of the ORIGINAL fixed point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedShiftedSourcePoints

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow MNEC.NativePrimitiveAreaCharts
open NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences
open NativePrimitiveRectangles
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

def sourcePhase (x : CompleteOrbits q v) (a : ℕ → ℝ) (n : ℕ) : CompleteOrbits q v :=
  timeMap q v (a n / NativeTeichmullerRay.contraction v (t n)) x

def point (x : CompleteOrbits q v) (a : ℕ → ℝ) (n : ℕ) : Regular (fiberForm π F hBranch (p n)) :=
  BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e (sourcePhase q v t x a n).val n

def time (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x : CompleteOrbits q v)
    (a : ℕ → ℝ) (h : ℝ) (n : ℕ) : ℝ :=
  (a n + h - (coordinate π F hBranch s (inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x a n).val)).2) /
    NativeTeichmullerRay.contraction v (t n)

theorem point_eq_target_trajectory (x : CompleteOrbits q v) (a : ℕ → ℝ) (n : ℕ) :
    point π F hBranch q v hv t p e x a n =
      trajectory (fiberForm π F hBranch (p n)) vertical
        (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x.val n) (a n) := by
  have hk := (NativeTeichmullerRay.contraction_pos v hv (t n)).ne'
  have hvel : planeEquiv (NativeTeichmullerRay.matrix v hv (t n)) v =
      NativeTeichmullerRay.contraction v (t n) • vertical := by
    simpa only [NativeTeichmullerRay.vertical, vertical] using NativeTeichmullerRay.contracted_velocity v hv (t n)
  have hc := NativeSL2ArcTransport.trajectory_clock q (NativeTeichmullerRay.matrix v hv (t n))
    (fiberForm π F hBranch (p n)) (e n) hk hvel x.val (a n / NativeTeichmullerRay.contraction v (t n))
    (complete_time_mem q v x _)
  simpa only [point, sourcePhase, timeMap_value, BeltramiMarkedRayOrbitCounts.point,
    div_mul_cancel₀ _ hk] using hc

theorem native_time (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (n : ℕ) (i : Index (fiberForm π F hBranch (p n))) (x : CompleteOrbits q v) (a : ℕ → ℝ) (h : ℝ)
    (hfun : ∀ z, chart (fiberForm π F hBranch (p n)) i z =
      coordinate π F hBranch s (inclusion π F hBranch (p n) z.val)) :
    NativeShiftedRayOrbitCounts.time q v hv (t n) (fiberForm π F hBranch (p n)) (e n) i
      (sourcePhase q v t x a n).val h + a n / NativeTeichmullerRay.contraction v (t n) =
        time π F hBranch q v hv t p e s x a h n := by
  change (h - (chart (fiberForm π F hBranch (p n)) i (point π F hBranch q v hv t p e x a n)).2) /
    NativeTeichmullerRay.contraction v (t n) + a n / NativeTeichmullerRay.contraction v (t n) = _
  rw [hfun]
  unfold time
  ring

theorem interval_length (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (x : CompleteOrbits q v) (a : ℕ → ℝ) (lo hi : ℝ) (n : ℕ) :
    time π F hBranch q v hv t p e s x a hi n - time π F hBranch q v hv t p e s x a lo n =
      BeltramiMarkedShiftedClocks.length v t lo hi n := by
  unfold time BeltramiMarkedShiftedClocks.length
  ring

theorem time_ratio_tendsto (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (p₀ : Base A) (x₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (x : CompleteOrbits q v) (a : ℕ → ℝ) {a₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (h : ℝ)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x a n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ x₀))) :
    Tendsto (fun n => time π F hBranch q v hv t p e s x a h n / NativeRayReferenceTimes.reference v (t n))
      atTop (𝓝 (a₀ + h - (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).2)) := by
  have hcoord := BeltramiMarkedSliceCoordinates.coordinate_tendsto π F hBranch s hx₀ hx
  exact NativeRayReferenceTimes.lifted_ratio_tendsto v hv t _ ((ha.add_const h).sub hcoord.snd_nhds)

end VeechDichotomy.BeltramiMarkedShiftedSourcePoints
