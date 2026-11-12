module

public import VeechDichotomy.BeltramiMarkedLimitFlatCharts
public import VeechDichotomy.BeltramiMarkedFlatArea

/-! Every neighborhood of a genuine regular limit point contains flat
regions of the SAME strictly positive physical area in all nearby
native fibers. This is a consequence of the constructed family, actual
forms and canonical area, not an additional flat-limit hypothesis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedPositiveFlatRegions

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas MNEC.LatticeTorus
open NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory Metric
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem regions (p : Base A) (hzero : ∀ i, p.2.val.2 i = 0)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) (hx : x ∈ regularSet (fiberForm π F hBranch p))
    {W : Set (Total π F hBranch)} (hW : IsOpen W) (hxW : inclusion π F hBranch p x ∈ W) :
    ∃ U : Set (Base A), IsOpen U ∧ p ∈ U ∧ ∃ (v₀ : Plane) (r : ℝ), 0 < r ∧ 0 < volume (ball v₀ r) ∧
      ∀ q ∈ U, ∃ i : MNEC.NativePrimitiveAreaCharts.Index (fiberForm π F hBranch q),
        i.2.chart = BeltramiMarkedScaledSlices.chart π F hBranch (p.2, x.point) q ∧
        MNEC.NativeRegularArea.regularArea (fiberForm π F hBranch q)
          ((MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch q) i).symm '' ball v₀ r) = volume (ball v₀ r) ∧
        ∀ v ∈ ball v₀ r, inclusion π F hBranch q
          (((MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch q) i).symm v).val) ∈ W := by
  let s := (p.2, x.point)
  let c := BeltramiMarkedScaledSlices.chart π F hBranch s p
  let z₀ := c x
  let v₀ := toPlane z₀
  have hcx : x ∈ c.source := BeltramiMarkedLimitFlatCharts.center π F hBranch p x
  have hz₀ : z₀ ∈ c.target := c.map_source hcx
  let H : Base A × Plane → Base A × ℂ := fun t => (t.1, toPlane.symm t.2)
  have hH : Continuous H := continuous_fst.prodMk (toPlane.symm.continuous.comp continuous_snd)
  let D := H ⁻¹' (BeltramiMarkedUniformSlices.domain π F hBranch s ∩ BeltramiMarkedUniformSlices.inverse π F hBranch s ⁻¹' W)
  have hD : IsOpen D :=
    ((BeltramiMarkedUniformSlices.continuousOn_inverse π F hBranch s).isOpen_inter_preimage
      (BeltramiMarkedUniformSlices.domain_open π F hBranch s) hW).preimage hH
  have hbase : (p, v₀) ∈ D := by
    change (p, toPlane.symm (toPlane z₀)) ∈
      BeltramiMarkedUniformSlices.domain π F hBranch s ∩ BeltramiMarkedUniformSlices.inverse π F hBranch s ⁻¹' W
    rw [ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨hz₀, ?_⟩
    change BeltramiMarkedUniformSlices.inverse π F hBranch s (p, z₀) ∈ W
    rw [BeltramiMarkedUniformSlices.inverse_value π F hBranch s p hz₀]
    change inclusion π F hBranch p (c.symm (c x)) ∈ W
    rwa [c.left_inv hcx]
  obtain ⟨U, V, hU, hV, hpU, hvV, hUV⟩ := isOpen_prod_iff.mp hD p v₀ hbase
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV v₀ hvV
  have hvol : 0 < volume (ball v₀ r) :=
    pos_iff_ne_zero.mpr (isOpen_ball.measure_ne_zero volume ⟨v₀, mem_ball_self hr⟩)
  refine ⟨U, hU, hpU, v₀, r, hr, hvol, ?_⟩
  intro q hq
  have htarget : ∀ v ∈ ball v₀ r, toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s q).target :=
    fun v hv => (hUV (show (q, v) ∈ U ×ˢ V from ⟨hq, hball hv⟩)).1
  have hzq : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s q).target := by
    simpa only [v₀, ContinuousLinearEquiv.symm_apply_apply] using htarget v₀ (mem_ball_self hr)
  have hy := BeltramiMarkedLimitFlatCharts.original_regular π F hBranch p hzero hx
  have hs : s.2 ∉ criticalSet π := fun hc => hy (critical_subset_zeroSet π hc)
  have hreg := BeltramiMarkedLimitFlatCharts.base_regular π F p.2 hzero hy
  let i := BeltramiMarkedFlatArea.index π F hBranch s hs hreg q z₀ hzq
  refine ⟨i, rfl, ?_, ?_⟩
  · exact BeltramiMarkedFlatArea.area_image π F hBranch s hs hreg q z₀ hzq _ isOpen_ball.measurableSet htarget
  · intro v hv
    have hw := (hUV (show (q, v) ∈ U ×ˢ V from ⟨hq, hball hv⟩)).2
    change BeltramiMarkedUniformSlices.inverse π F hBranch s (q, toPlane.symm v) ∈ W at hw
    rw [BeltramiMarkedUniformSlices.inverse_value π F hBranch s q (htarget v hv)] at hw
    change inclusion π F hBranch q (((BeltramiMarkedFlatArea.chart π F hBranch s hs hreg q z₀ hzq).symm v).val) ∈ W
    rw [BeltramiMarkedFlatArea.inverse_value π F hBranch s hs hreg q z₀ hzq v (htarget v hv)]
    exact hw

end VeechDichotomy.BeltramiMarkedPositiveFlatRegions
