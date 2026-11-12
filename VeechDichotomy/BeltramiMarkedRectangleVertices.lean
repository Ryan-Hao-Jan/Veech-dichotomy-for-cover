module

public import VeechDichotomy.BeltramiMarkedFlatArea
public import VeechDichotomy.BeltramiMarkedSliceCoordinates
public import VeechDichotomy.NativeRayRectangleComparison

/-! Actual convergent fiber points give valid ordered rectangle vertices
in the fixed primitive charts on all nearby fibers. Target persistence,
source membership, coordinates and positive lifted-height divergence
are derived from actual total-space convergence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRectangleVertices

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativePrimitiveRectangles
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem eventual_vertices (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {l r bot top : ℝ}
    (hR : ∀ a ∈ Icc l r ×ˢ Icc bot top, toPlane.symm a ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hxR : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀) ∈ rectangle l r bot top)
    (hyR : coordinate π F hBranch s (inclusion π F hBranch p₀ y₀) ∈ rectangle l r bot top)
    (horder : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1 < (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1)
    (p : ℕ → Base A) (x y : ∀ n, Regular (fiberForm π F hBranch (p n)))
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (x n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (y n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀))) :
    ∀ᶠ n in atTop, ∃ i : MNEC.NativePrimitiveAreaCharts.Index (fiberForm π F hBranch (p n)),
      (∀ z, MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i z = coordinate π F hBranch s (inclusion π F hBranch (p n) z.val)) ∧
      x n ∈ (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i).source ∧
      y n ∈ (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i).source ∧
      rectangle l r bot top ⊆ (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i).target ∧
      MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (x n) ∈ rectangle l r bot top ∧
      MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (y n) ∈ rectangle l r bot top ∧
      (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (x n)).1 <
        (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i (y n)).1 := by
  have hxS : inclusion π F hBranch p₀ x₀ ∈ source π F hBranch s := hx₀
  have hyS : inclusion π F hBranch p₀ y₀ ∈ source π F hBranch s := hy₀
  have hcx := coordinate_tendsto π F hBranch s hxS hx
  have hcy := coordinate_tendsto π F hBranch s hyS hy
  have hp : Tendsto p atTop (𝓝 p₀) := by
    simpa only [Function.comp_def, projection_inclusion] using (projection_holomorphic π F hBranch).continuous.continuousAt.tendsto.comp hx
  have hgap := hcy.fst_nhds.sub hcx.fst_nhds
  have hgapPos := hgap (Ioi_mem_nhds (sub_pos.mpr horder))
  let K := toPlane.symm '' (Icc l r ×ˢ Icc bot top)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image toPlane.symm.continuous
  have hsub : K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target := by
    rintro _ ⟨a, ha, rfl⟩
    exact hR a ha
  obtain ⟨U, hU, hpU, hUK⟩ := BeltramiMarkedUniformSlices.compact_persistence π F hBranch s p₀ hK hsub
  have hrectOpen : IsOpen (rectangle l r bot top) := isOpen_Ioo.prod isOpen_Ioo
  filter_upwards [eventually_source π F hBranch s hxS hx, eventually_source π F hBranch s hyS hy,
    hcx (hrectOpen.mem_nhds hxR), hcy (hrectOpen.mem_nhds hyR), hgapPos, hp (hU.mem_nhds hpU)] with n hnX hnY hnRX hnRY hnOrd hnU
  have hxn : (x n).val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s (p n)).source := hnX
  have hyn : (y n).val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s (p n)).source := hnY
  let i := BeltramiMarkedFlatArea.index π F hBranch s hs hreg (p n) _
    ((BeltramiMarkedScaledSlices.chart π F hBranch s (p n)).map_source hxn)
  have hfun : ∀ z, MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch (p n)) i z =
      coordinate π F hBranch s (inclusion π F hBranch (p n) z.val) := fun _ => rfl
  refine ⟨i, hfun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MNEC.NativePrimitiveAreaCharts.chart_source]; exact hxn
  · rw [MNEC.NativePrimitiveAreaCharts.chart_source]; exact hyn
  · intro a ha
    rw [MNEC.NativePrimitiveAreaCharts.chart_target]
    exact hUK (p n) hnU ⟨a, ⟨⟨ha.1.1.le, ha.1.2.le⟩, ⟨ha.2.1.le, ha.2.2.le⟩⟩, rfl⟩
  · rw [hfun]; exact hnRX
  · rw [hfun]; exact hnRY
  · rw [hfun, hfun]; exact sub_pos.mp hnOrd

theorem lifted_height_tendsto (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (p₀ : Base A) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (horder : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).2 < (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).2)
    (p : ℕ → Base A) (x y : ∀ n, Regular (fiberForm π F hBranch (p n)))
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (x n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (y n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀)))
    (v : Plane) (hv : v ≠ 0) {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => ((coordinate π F hBranch s (inclusion π F hBranch (p n) (y n).val)).2 -
      (coordinate π F hBranch s (inclusion π F hBranch (p n) (x n).val)).2) / NativeTeichmullerRay.contraction v (t n)) atTop atTop := by
  have hcx := coordinate_tendsto π F hBranch s hx₀ hx
  have hcy := coordinate_tendsto π F hBranch s hy₀ hy
  exact NativeRayRectangleComparison.lifted_time_tendsto v hv ht (hcy.snd_nhds.sub hcx.snd_nhds) (sub_pos.mpr horder)

end VeechDichotomy.BeltramiMarkedRectangleVertices
