module

public import VeechDichotomy.BeltramiMarkedRectangleVertices
public import VeechDichotomy.NativeRayOrbitComparison
public import VeechDichotomy.BoundedCountRates

/-! The concrete geometric rectangle comparison along ACTUAL returning
native rays in the constructed family. Two fixed source points with
ordered regular limits give equal-length forward/backward source orbit
segments whose lengths diverge and whose transverse intersection counts
differ by at most one. All rectangle/point hypotheses on nearby fibers
are derived from actual limit coordinates and total-space convergence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRayOrbitCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup
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

def point (x : Regular q) (n : ℕ) : Regular (fiberForm π F hBranch (p n)) :=
  NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix v hv (t n)) (fiberForm π F hBranch (p n)) (e n) x

def clock (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x y : Regular q) (n : ℕ) : ℝ :=
  ((coordinate π F hBranch s (inclusion π F hBranch (p n) (point π F hBranch q v hv t p e y n).val)).2 -
    (coordinate π F hBranch s (inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x n).val)).2) /
      NativeTeichmullerRay.contraction v (t n)

def forwardCount (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x y z : Regular q) (a b : ℝ) (n : ℕ) : ℕ :=
  (trajectory q v x '' Icc 0 (clock π F hBranch q v hv t p e s x y n) ∩
    trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard

def backwardCount (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x y z : Regular q) (a b : ℝ) (n : ℕ) : ℕ :=
  (trajectory q v y '' Icc (-(clock π F hBranch q v hv t p e s x y n)) 0 ∩
    trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard

theorem comparison (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {l r bot top : ℝ}
    (hR : ∀ a ∈ Icc l r ×ˢ Icc bot top, toPlane.symm a ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hxR : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀) ∈ NativePrimitiveRectangles.rectangle l r bot top)
    (hyR : coordinate π F hBranch s (inclusion π F hBranch p₀ y₀) ∈ NativePrimitiveRectangles.rectangle l r bot top)
    (hhor : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1 < (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1)
    (hver : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).2 < (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).2)
    (x y z : Regular q) (a b : ℝ)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q v hv t p e y n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀)))
    (ht : Tendsto t atTop atTop)
    (hI : Icc a b ⊆ domain q (NativeRayRectangleComparison.transverse v hv) z)
    (hinj : InjOn (trajectory q (NativeRayRectangleComparison.transverse v hv) z) (Icc a b)) :
    Tendsto (clock π F hBranch q v hv t p e s x y) atTop atTop ∧
      ∀ᶠ n in atTop,
        forwardCount π F hBranch q v hv t p e s x y z a b n ≤ backwardCount π F hBranch q v hv t p e s x y z a b n + 1 ∧
        backwardCount π F hBranch q v hv t p e s x y z a b n ≤ forwardCount π F hBranch q v hv t p e s x y z a b n + 1 := by
  have htime := BeltramiMarkedRectangleVertices.lifted_height_tendsto π F hBranch s p₀ x₀ y₀ hx₀ hy₀ hver
    p (point π F hBranch q v hv t p e x) (point π F hBranch q v hv t p e y) hx hy v hv ht
  have hvertices := BeltramiMarkedRectangleVertices.eventual_vertices π F hBranch s hs hreg p₀ x₀ y₀ hx₀ hy₀ hR hxR hyR hhor
    p (point π F hBranch q v hv t p e x) (point π F hBranch q v hv t p e y) hx hy
  refine ⟨htime, ?_⟩
  filter_upwards [hvertices] with n hn
  obtain ⟨i, hfun, hxn, hyn, hRn, hxr, hyr, horder⟩ := hn
  have hxside : point π F hBranch q v hv t p e x n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (point π F hBranch q v hv t p e x n)).1 bot top :=
    ⟨hxn, rfl, hxr.2⟩
  have hyside : point π F hBranch q v hv t p e y n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (point π F hBranch q v hv t p e y n)).1 bot top :=
    ⟨hyn, rfl, hyr.2⟩
  have hcounts := NativeRayOrbitComparison.opposite_orbit_counts q v hv (t n) (fiberForm π F hBranch (p n)) (e n) i x y z a b
    hI hinj hxr.1 hyr.1 horder hRn hxside hyside
  have hclock : NativeRayOrbitComparison.segmentTime q v hv (t n) (fiberForm π F hBranch (p n)) (e n) i x y =
      clock π F hBranch q v hv t p e s x y n := by
    change ((MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (point π F hBranch q v hv t p e y n)).2 -
      (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (point π F hBranch q v hv t p e x n)).2) /
        NativeTeichmullerRay.contraction v (t n) = _
    rw [hfun, hfun]
    rfl
  rw [hclock] at hcounts
  exact hcounts

end VeechDichotomy.BeltramiMarkedRayOrbitCounts
