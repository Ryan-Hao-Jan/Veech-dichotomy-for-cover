module

public import VeechDichotomy.HolomorphicCurveMaps
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! A holomorphic germ between genuine complex curves is analytically
smooth. The Cauchy argument is local, so it applies to partial chart maps
and their inverses without an artificial global differentiability premise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCurveGerms

open Set Filter Topology
open scoped Manifold ContDiff

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

theorem contMDiffAt_of_eventually_mdifferentiable {f : X → Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let c := chartAt ℂ x
  let d := chartAt ℂ (f x)
  have hc : x ∈ c.source := mem_chart_source ℂ x
  have hct : c x ∈ c.target := c.map_source hc
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv hc] using (c.symm.continuousAt hct).tendsto
  have hnearF := ht hf
  have hnearTarget : ∀ᶠ z in 𝓝 (c x), f (c.symm z) ∈ d.source :=
    (hf.self_of_nhds.continuousAt.tendsto.comp ht) (d.open_source.mem_nhds (mem_chart_source ℂ (f x)))
  have hnear : ∀ᶠ z in 𝓝 (c x), DifferentiableAt ℂ (d ∘ f ∘ c.symm) z := by
    filter_upwards [c.open_target.mem_nhds hct, hnearF, hnearTarget] with z hz hFz hDz
    have hci := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) hz
    have hd := mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (f x)) hDz
    exact (hd.comp z (hFz.comp z hci)).differentiableAt
  obtain ⟨U, hsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  have hdiff : DifferentiableOn ℂ (d ∘ f ∘ c.symm) U := fun z hz => (hsub hz).differentiableWithinAt
  exact HolomorphicCurveMaps.contMDiffAt_of_analytic_chart hf.self_of_nhds.continuousAt
    (hdiff.analyticAt (hU.mem_nhds hxU))

theorem chart_contMDiffAt (e : OpenPartialHomeomorph X Y) (he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    {x : X} (hx : x ∈ e.source) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x := by
  apply contMDiffAt_of_eventually_mdifferentiable
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact he.mdifferentiableAt hy

theorem chart_contMDiffAt_symm (e : OpenPartialHomeomorph X Y) (he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    {y : Y} (hy : y ∈ e.target) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm y := by
  apply contMDiffAt_of_eventually_mdifferentiable
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact he.mdifferentiableAt_symm hz

end VeechDichotomy.HolomorphicCurveGerms
