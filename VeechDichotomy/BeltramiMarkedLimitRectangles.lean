module

public import VeechDichotomy.BeltramiMarkedLimitFlatCharts
public import VeechDichotomy.BeltramiMarkedSliceCoordinates
public import VeechDichotomy.NativePrimitiveRectangles

/-! Concrete good fixed-slice rectangles on the actual limit fiber.
Every regular zero-displacement limit point lies in one. Their actual
total-space regions are open, so overlap neighborhoods persist and can
be used by the conull source-point selection theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedLimitRectangles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativePrimitiveRectangles
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

structure Rectangle (p₀ : Base A) where
  slice : ComplexBeltramiMarkParameters.Parameters A × Y
  not_critical : slice.2 ∉ criticalSet π
  base_regular : BeltramiMarkedRegularSlices.baseCenter π F slice ∈ regularSet qX
  (left right bottom top : ℝ)
  width_pos : left < right
  height_pos : bottom < top
  target : ∀ c ∈ Icc left right ×ˢ Icc bottom top,
    toPlane.symm c ∈ (BeltramiMarkedScaledSlices.chart π F hBranch slice p₀).target

namespace Rectangle

variable {π F hBranch} {p₀ : Base A} (B : Rectangle π F hBranch p₀)

def totalRegion : Set (Total π F hBranch) :=
  source π F hBranch B.slice ∩ coordinate π F hBranch B.slice ⁻¹' rectangle B.left B.right B.bottom B.top

def region : Set (BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) :=
  inclusion π F hBranch p₀ ⁻¹' B.totalRegion

def regularRegion : Set (Regular (fiberForm π F hBranch p₀)) := Subtype.val ⁻¹' B.region

theorem totalRegion_open : IsOpen B.totalRegion :=
  (continuousOn_coordinate π F hBranch B.slice).isOpen_inter_preimage (source_open π F hBranch B.slice)
    (isOpen_Ioo.prod isOpen_Ioo)

theorem region_open : IsOpen B.region :=
  B.totalRegion_open.preimage (holomorphic_inclusion π F hBranch p₀).continuous

theorem regularRegion_open : IsOpen B.regularRegion := B.region_open.preimage continuous_subtype_val

theorem region_regular : B.region ⊆ regularSet (fiberForm π F hBranch p₀) :=
  fun _ hx => BeltramiMarkedScaledSlices.regular_source π F hBranch B.slice B.not_critical B.base_regular p₀ hx.1

end Rectangle

theorem closed_rectangle_in_open (z : Plane) {V : Set Plane} (hV : IsOpen V) (hz : z ∈ V) :
    ∃ l r bot top : ℝ, z ∈ rectangle l r bot top ∧ Icc l r ×ˢ Icc bot top ⊆ V := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds hz)
  obtain ⟨l0, r0, hlr, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp hP
  obtain ⟨b0, t0, hbt, hJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp hQ
  change z.1 ∈ Ioo l0 r0 at hlr
  change z.2 ∈ Ioo b0 t0 at hbt
  refine ⟨(l0 + z.1) / 2, (z.1 + r0) / 2, (b0 + z.2) / 2, (z.2 + t0) / 2, ?_, ?_⟩
  · exact ⟨⟨by linarith [hlr.1], by linarith [hlr.2]⟩,
      ⟨by linarith [hbt.1], by linarith [hbt.2]⟩⟩
  · intro w hw
    apply hPQ
    exact ⟨hI ⟨by linarith [hw.1.1, hlr.1], by linarith [hw.1.2, hlr.2]⟩,
      hJ ⟨by linarith [hw.2.1, hbt.1], by linarith [hw.2.2, hbt.2]⟩⟩

theorem covers_regular (p₀ : Base A) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (x : Regular (fiberForm π F hBranch p₀)) :
    ∃ B : Rectangle π F hBranch p₀, x ∈ B.regularRegion := by
  let s : ComplexBeltramiMarkParameters.Parameters A × Y := (p₀.2, x.val.point)
  have hregOld := BeltramiMarkedLimitFlatCharts.original_regular π F hBranch p₀ hzero x.property
  have hs : s.2 ∉ criticalSet π := fun hc => hregOld (critical_subset_zeroSet π hc)
  have hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX :=
    BeltramiMarkedLimitFlatCharts.base_regular π F p₀.2 hzero hregOld
  let c := BeltramiMarkedScaledSlices.chart π F hBranch s p₀
  have hx : x.val ∈ c.source := BeltramiMarkedLimitFlatCharts.center π F hBranch p₀ x.val
  have hV : IsOpen (toPlane.symm ⁻¹' c.target) := c.open_target.preimage toPlane.symm.continuous
  have hxV : toPlane (c x.val) ∈ toPlane.symm ⁻¹' c.target := by
    change toPlane.symm (toPlane (c x.val)) ∈ c.target
    rw [toPlane.symm_apply_apply]
    exact c.map_source hx
  obtain ⟨l, r, bot, top, hxR, hR⟩ := closed_rectangle_in_open (toPlane (c x.val)) hV hxV
  let B : Rectangle π F hBranch p₀ := {
    slice := s, not_critical := hs, base_regular := hreg
    left := l, right := r, bottom := bot, top := top
    width_pos := hxR.1.1.trans hxR.1.2
    height_pos := hxR.2.1.trans hxR.2.2
    target := fun z hz => hR hz }
  refine ⟨B, ?_⟩
  change x.val ∈ c.source ∧ toPlane (c x.val) ∈ rectangle l r bot top
  exact ⟨hx, hxR⟩

end VeechDichotomy.BeltramiMarkedLimitRectangles
