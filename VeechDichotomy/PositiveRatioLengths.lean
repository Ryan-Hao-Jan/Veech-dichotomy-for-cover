module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-! A positive limiting ratio to a divergent clock forces divergence.
In particular, two separated endpoint ratios give intervals of
divergent positive length. -/

@[expose] public section

namespace VeechDichotomy.PositiveRatioLengths

open Filter Topology

theorem divergent {I : Type*} {l : Filter I} {R T : I → ℝ} {a : ℝ}
    (hR : Tendsto R l atTop) (hT : Tendsto (fun i => T i / R i) l (𝓝 a)) (ha : 0 < a) :
    Tendsto T l atTop := by
  have hprod := hT.pos_mul_atTop ha hR
  apply Tendsto.congr' _ hprod
  filter_upwards [hR.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
  exact div_mul_cancel₀ (T i) hi.ne'

theorem interval_divergent {I : Type*} {l : Filter I} {R A B : I → ℝ} {a b : ℝ}
    (hR : Tendsto R l atTop) (hA : Tendsto (fun i => A i / R i) l (𝓝 a))
    (hB : Tendsto (fun i => B i / R i) l (𝓝 b)) (hab : a < b) :
    Tendsto (fun i => B i - A i) l atTop := by
  apply divergent hR _ (sub_pos.mpr hab)
  simpa only [sub_div] using hB.sub hA

end VeechDichotomy.PositiveRatioLengths
