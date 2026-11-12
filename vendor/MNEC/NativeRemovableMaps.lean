module

public import MNEC.NativeDifferentialEquiv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Complex-curve maps extend holomorphically across finite exceptional
sets when the actual whole-curve map is continuous. This applies to the
computed physical twist homeomorphism, preserving its literal underlying
map rather than selecting an unrelated geometric realization. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeRemovableMaps

open Set Filter Topology
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

omit [T2Space X] [T2Space Y] in
theorem mdifferentiableAt_of_punctured (f : X → Y) (x : X) (hc : ContinuousAt f x)
    (hd : ∀ᶠ y in 𝓝[≠] x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
  let e := chartAt ℂ x
  let d := chartAt ℂ (f x)
  let a := e x
  let g : ℂ → ℂ := fun z => d (f (e.symm z))
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hfx : f x ∈ d.source := mem_chart_source ℂ (f x)
  have ha : a ∈ e.target := e.map_source hx
  have hinv : e.symm a = x := e.left_inv hx
  have hec : ContinuousAt e.symm a := e.symm.continuousOn.continuousAt (e.open_target.mem_nhds ha)
  have hfc : ContinuousAt (fun z => f (e.symm z)) a := by
    have h : ContinuousAt f (e.symm a) := by rw [hinv]; exact hc
    exact h.comp hec
  have hgc : ContinuousAt g a := by
    have h : ContinuousAt d (f (e.symm a)) := by
      rw [hinv]
      exact d.continuousOn.continuousAt (d.open_source.mem_nhds hfx)
    exact h.comp (f := fun z : ℂ => f (e.symm z)) hfc
  have hsource : ∀ᶠ z in 𝓝 a, f (e.symm z) ∈ d.source := by
    apply hfc
    change d.source ∈ 𝓝 (f (e.symm a))
    rw [hinv]
    exact d.open_source.mem_nhds hfx
  have hd' : ∀ᶠ y in 𝓝 x, y ≠ x → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    eventually_nhdsWithin_iff.mp hd
  have hpull : ∀ᶠ z in 𝓝 a, e.symm z ≠ x → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (e.symm z) := by
    have h : ∀ᶠ y in 𝓝 (e.symm a), y ≠ x → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y := by
      rw [hinv]
      exact hd'
    exact hec h
  have hgd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ g z := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds ha),
      eventually_nhdsWithin_of_eventually_nhds hsource,
      eventually_nhdsWithin_of_eventually_nhds hpull] with z hne hz hdz hdf
    have hzx : e.symm z ≠ x := by
      intro h
      apply hne
      calc
        z = e (e.symm z) := (e.right_inv hz).symm
        _ = a := congrArg e h
    have heD := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) hz
    have hdD := mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (f x)) hdz
    have h := hdD.comp z ((hdf hzx).comp z heD)
    exact h.differentiableAt
  have hgD := (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc).differentiableAt
  have heD := mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) hx
  have hcomp := hgD.mdifferentiableAt.comp x heD
  have hgval : g (e x) = d (f x) := by
    change d (f (e.symm (e x))) = d (f x)
    rw [e.left_inv hx]
  have htarget : g (e x) ∈ d.target := by rw [hgval]; exact d.map_source hfx
  have hdD := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (f x)) htarget
  apply (hdD.comp x hcomp).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx, hc (d.open_source.mem_nhds hfx)] with y hy hfy
  change f y = d.symm (d (f (e.symm (e y))))
  rw [e.left_inv hy, d.left_inv hfy]

omit [T2Space Y] in
theorem mdifferentiable_of_continuous_off_finite (f : X → Y) (hc : Continuous f)
    (S : Set X) (hS : S.Finite)
    (hd : ∀ x, x ∉ S → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro x
  apply mdifferentiableAt_of_punctured f x hc.continuousAt
  have hclosed : IsClosed (S \ {x}) := (hS.sdiff).isClosed
  have hnear : (S \ {x})ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds hnear] with y hy hys
  apply hd y
  intro hyS
  exact hys ⟨hyS, hy⟩

end MNEC.NativeRemovableMaps

