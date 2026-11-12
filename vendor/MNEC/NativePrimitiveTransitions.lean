module

public import MNEC.RegularPrimitiveCharts
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Genuine primitive charts of an arbitrary native holomorphic differential
have local translation overlaps. Their equal intrinsic cotangent derivatives
make their difference locally constant in an original complex curve chart.
No inverse-differentiability, translation-atlas, or splitting premise is used. -/

@[expose] public section
noncomputable section
namespace MNEC.NativePrimitiveTransitions

open NativeAbelianDifferential Set Filter Metric
open scoped Manifold ContDiff Topology Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A primitive chart certified only by the actual differential identity.
The existing analytic primitive/IFT theorem constructs it at every regular
point; translation compatibility is proved below rather than a field. -/
structure PrimitiveChart (q : Differential X) (x : ↥(regularSet q)) where
  chart : OpenPartialHomeomorph X ℂ
  center : x.val ∈ chart.source
  regular_source : chart.source ⊆ regularSet q
  derivative : ∀ y ∈ chart.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) chart y (q.val.toFun y)

theorem exists_primitiveChart (q : Differential X) (x : ↥(regularSet q)) : Nonempty (PrimitiveChart q x) := by
  obtain ⟨e, hex, hreg, hder⟩ := RegularPrimitiveCharts.exists_native_translation_chart q x.val x.property
  exact ⟨⟨e, hex, hreg, hder⟩⟩

def chosen (q : Differential X) (x : ↥(regularSet q)) : PrimitiveChart q x :=
  Classical.choice (exists_primitiveChart q x)

/-- Equal native cotangent derivatives force a local constant difference,
proved in a genuine original complex chart by the mean-value theorem. -/
theorem difference_germ (q : Differential X) (e f : OpenPartialHomeomorph X ℂ)
    (he : ∀ y ∈ e.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) e y (q.val.toFun y))
    (hf : ∀ y ∈ f.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) f y (q.val.toFun y))
    (x : X) (hx : x ∈ e.source ∩ f.source) :
    ∀ᶠ y in 𝓝 x, f y = e y + (f x - e x) := by
  let c := chartAt ℂ x
  let U := e.source ∩ f.source
  let V := c.target ∩ c.symm ⁻¹' U
  let a := c x
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hU : IsOpen U := e.open_source.inter f.open_source
  have hV : IsOpen V := c.symm.continuousOn.isOpen_inter_preimage c.open_target hU
  have haV : a ∈ V := ⟨c.map_source hcx, by change c.symm (c x) ∈ U; rw [c.left_inv hcx]; exact hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  let h : ℂ → ℂ := fun z => f (c.symm z) - e (c.symm z)
  have hder : ∀ z ∈ ball a r, HasFDerivAt h (0 : ℂ →L[ℂ] ℂ) z := by
    intro z hz
    have hzV := hball hz
    have hsub := (hf _ hzV.2.2).sub (he _ hzV.2.1)
    have hcInv := (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) hzV.1).hasMFDerivAt
    have hcomp := hsub.comp z hcInv
    have hzero : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) h z (0 : ℂ →L[ℂ] ℂ) := by
      simpa only [Function.comp_def, sub_self, ContinuousLinearMap.zero_comp] using! hcomp
    exact hzero.hasFDerivAt
  have hconst : ∀ z ∈ ball a r, h z = h a := by
    intro z hz
    apply (convex_ball a r).is_const_of_fderivWithin_eq_zero
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt) _ hz (mem_ball_self hr)
    intro u hu
    rw [fderivWithin_of_isOpen isOpen_ball hu]
    exact (hder u hu).fderiv
  have hcCont : ContinuousAt c x := c.continuousOn.continuousAt (c.open_source.mem_nhds hcx)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ c y ∈ ball a r := by
    filter_upwards [c.open_source.mem_nhds hcx, hcCont (isOpen_ball.mem_nhds (mem_ball_self hr))] with y hy hyB
    exact ⟨hy, hyB⟩
  filter_upwards [hnear] with y hy
  have hvalue := hconst (c y) hy.2
  change f (c.symm (c y)) - e (c.symm (c y)) = f (c.symm (c x)) - e (c.symm (c x)) at hvalue
  rw [c.left_inv hy.1, c.left_inv hcx] at hvalue
  calc
    f y = (f y - e y) + e y := by abel
    _ = (f x - e x) + e y := by rw [hvalue]
    _ = e y + (f x - e x) := add_comm _ _

/-- Actual complex translation germ on the overlap of two constructed
primitive charts. Only their proved intrinsic derivative identities enter. -/
theorem transition_germ (q : Differential X) (e f : OpenPartialHomeomorph X ℂ)
    (he : ∀ y ∈ e.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) e y (q.val.toFun y))
    (hf : ∀ y ∈ f.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) f y (q.val.toFun y))
    (p : ℂ) (hp : p ∈ (e.symm.trans f).source) :
    ∃ a : ℂ, ∀ᶠ z in 𝓝 p, (e.symm.trans f) z = z + a := by
  let x := e.symm p
  have hx : x ∈ e.source ∩ f.source := ⟨e.map_target hp.1, hp.2⟩
  have hd := difference_germ q e f he hf x hx
  have hc : ContinuousAt e.symm p := e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hp.1)
  refine ⟨f x - e x, ?_⟩
  filter_upwards [e.open_target.mem_nhds hp.1, hc hd] with z hz hdiff
  change f (e.symm z) = z + _
  rw [hdiff, e.right_inv hz]

end MNEC.NativePrimitiveTransitions
