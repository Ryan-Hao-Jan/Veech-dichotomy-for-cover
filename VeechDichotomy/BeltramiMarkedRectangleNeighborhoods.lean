module

public import VeechDichotomy.BeltramiMarkedSliceCoordinates
public import VeechDichotomy.NativePrimitiveRectangles
public import Mathlib.Order.Interval.Set.Infinite

/-! Actual open total-space rectangle neighborhoods avoiding two
prescribed horizontal coordinates. Every genuine nonempty closed target
rectangle contains a regular fiber point in such a neighborhood. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRectangleNeighborhoods

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Topology
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

def region (s : ComplexBeltramiMarkParameters.Parameters A × Y) (l r bot top a b : ℝ) :
    Set (Total π F hBranch) :=
  source π F hBranch s ∩ coordinate π F hBranch s ⁻¹' ((Ioo l r \ {a, b}) ×ˢ Ioo bot top)

theorem region_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) (l r bot top a b : ℝ) :
    IsOpen (region π F hBranch s l r bot top a b) :=
  (continuousOn_coordinate π F hBranch s).isOpen_inter_preimage (source_open π F hBranch s)
    ((isOpen_Ioo.sdiff ((finite_singleton b).insert a).isClosed).prod isOpen_Ioo)

theorem exists_regular_point (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) {l r bot top : ℝ} (hlr : l < r) (hbt : bot < top)
    (hR : ∀ c ∈ Icc l r ×ˢ Icc bot top, toPlane.symm c ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (a b : ℝ) : ∃ z : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      z ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ z ∈ region π F hBranch s l r bot top a b := by
  obtain ⟨c, hc, hcab⟩ := (Ioo_infinite hlr).exists_notMem_finite ((finite_singleton b).insert a)
  have hd : (bot + top) / 2 ∈ Ioo bot top := by constructor <;> linarith
  have hp : toPlane.symm (c, (bot + top) / 2) ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target :=
    hR _ ⟨⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  let z := (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).symm (toPlane.symm (c, (bot + top) / 2))
  have hz : z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source :=
    (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).map_target hp
  have hcoord : coordinate π F hBranch s (inclusion π F hBranch p₀ z) = (c, (bot + top) / 2) := by
    rw [coordinate_inclusion, (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).right_inv hp,
      toPlane.apply_symm_apply]
  refine ⟨z, BeltramiMarkedScaledSlices.regular_source π F hBranch s hs hreg p₀ hz, hz, ?_⟩
  change coordinate π F hBranch s (inclusion π F hBranch p₀ z) ∈ (Ioo l r \ {a, b}) ×ˢ Ioo bot top
  rw [hcoord]
  exact ⟨⟨hc, hcab⟩, hd⟩

end VeechDichotomy.BeltramiMarkedRectangleNeighborhoods
