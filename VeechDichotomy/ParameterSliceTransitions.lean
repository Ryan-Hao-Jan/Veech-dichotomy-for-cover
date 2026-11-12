module

public import VeechDichotomy.ParameterSliceChart
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic

/-! Analytic transitions of actual parameter slices are restrictions
of the actual total-space transitions. The two chart centers need not
have the same parameter as the sliced fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ParameterSliceTransitions

open Set Filter Topology
open scoped ContDiff

section Topological

variable {P S Y Z : Type*} [TopologicalSpace P] [TopologicalSpace S]
  [TopologicalSpace Y] [TopologicalSpace Z]
variable (c : P → S) (hc : Function.Injective c)
  (e d : OpenPartialHomeomorph (P × Y) (S × Z))
  (he : ∀ x ∈ e.source, (e x).1 = c x.1) (hd : ∀ x ∈ d.source, (d x).1 = c x.1)

theorem transition_source (a : P) {z : Z}
    (hz : z ∈ ((ParameterSliceChart.chart c hc e he a).symm.trans (ParameterSliceChart.chart c hc d hd a)).source) :
    (c a, z) ∈ (e.symm.trans d).source := by
  refine ⟨hz.1, ?_⟩
  change e.symm (c a, z) ∈ d.source
  rw [ParameterSliceChart.inverse_pair c hc e he a hz.1]
  exact hz.2

theorem transition_value (a : P) {z : Z} (hz : z ∈ (ParameterSliceChart.chart c hc e he a).target) :
    ((e.symm.trans d) (c a, z)).2 =
      ((ParameterSliceChart.chart c hc e he a).symm.trans (ParameterSliceChart.chart c hc d hd a)) z := by
  rw [OpenPartialHomeomorph.trans_apply, ParameterSliceChart.inverse_pair c hc e he a hz]
  rfl

end Topological

section Analytic

variable {P S Y : Type*} [TopologicalSpace P] [NormedAddCommGroup S] [NormedSpace ℂ S]
  [TopologicalSpace Y]
variable (c : P → S) (hc : Function.Injective c)
  (e d : OpenPartialHomeomorph (P × Y) (S × ℂ))
  (he : ∀ x ∈ e.source, (e x).1 = c x.1) (hd : ∀ x ∈ d.source, (d x).1 = c x.1)

theorem transition_holomorphic (a : P) (z : ℂ)
    (hz : z ∈ ((ParameterSliceChart.chart c hc e he a).symm.trans (ParameterSliceChart.chart c hc d hd a)).source)
    (htotal : ContDiffAt ℂ ω (e.symm.trans d) (c a, z)) :
    ContDiffAt ℂ ω ((ParameterSliceChart.chart c hc e he a).symm.trans (ParameterSliceChart.chart c hc d hd a)) z := by
  have hslice : ContDiffAt ℂ ω (fun w : ℂ => (c a, w)) z := contDiffAt_const.prodMk contDiffAt_id
  have hcomp := contDiffAt_snd.comp z (htotal.comp z hslice)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(ParameterSliceChart.chart c hc e he a).open_target.mem_nhds hz.1] with w hw
  exact (transition_value c hc e d he hd a hw).symm

end Analytic
end VeechDichotomy.ParameterSliceTransitions
