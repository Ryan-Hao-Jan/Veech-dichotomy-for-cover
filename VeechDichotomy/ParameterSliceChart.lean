module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Slicing an actual parameter-preserving open partial homeomorphism
gives an actual open partial homeomorphism of each fiber. Inverse parameter
preservation is derived from injectivity and the actual right inverse. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ParameterSliceChart

open Set

variable {P S Y Z : Type*} [TopologicalSpace P] [TopologicalSpace S]
  [TopologicalSpace Y] [TopologicalSpace Z]
variable (c : P → S) (hc : Function.Injective c)
  (e : OpenPartialHomeomorph (P × Y) (S × Z))
  (hparameter : ∀ x ∈ e.source, (e x).1 = c x.1)

include hc hparameter in
theorem inverse_parameter (a : P) {z : Z} (hz : (c a, z) ∈ e.target) : (e.symm (c a, z)).1 = a := by
  apply hc
  exact (hparameter _ (e.map_target hz)).symm.trans (congrArg Prod.fst (e.right_inv hz))

include hc hparameter in
theorem inverse_pair (a : P) {z : Z} (hz : (c a, z) ∈ e.target) :
    e.symm (c a, z) = (a, (e.symm (c a, z)).2) :=
  Prod.ext (inverse_parameter c hc e hparameter a hz) rfl

def chart (a : P) : OpenPartialHomeomorph Y Z where
  toFun y := (e (a, y)).2
  invFun z := (e.symm (c a, z)).2
  source := {y | (a, y) ∈ e.source}
  target := {z | (c a, z) ∈ e.target}
  map_source' y hy := by
    have hp : (c a, (e (a, y)).2) = e (a, y) := Prod.ext (hparameter _ hy).symm rfl
    change (c a, (e (a, y)).2) ∈ e.target
    rw [hp]
    exact e.map_source hy
  map_target' z hz := by
    change (a, (e.symm (c a, z)).2) ∈ e.source
    rw [← inverse_pair c hc e hparameter a hz]
    exact e.map_target hz
  left_inv' y hy := by
    have hp : (c a, (e (a, y)).2) = e (a, y) := Prod.ext (hparameter _ hy).symm rfl
    change (e.symm (c a, (e (a, y)).2)).2 = y
    rw [hp, e.left_inv hy]
  right_inv' z hz := by
    rw [← inverse_pair c hc e hparameter a hz, e.right_inv hz]
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => hy)).snd
  continuousOn_invFun :=
    (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hz => hz)).snd

theorem chart_apply (a : P) (y : Y) : chart c hc e hparameter a y = (e (a, y)).2 := rfl

theorem chart_symm_apply (a : P) (z : Z) : (chart c hc e hparameter a).symm z = (e.symm (c a, z)).2 := rfl

theorem chart_source (a : P) (y : Y) : y ∈ (chart c hc e hparameter a).source ↔ (a, y) ∈ e.source := Iff.rfl

theorem chart_target (a : P) (z : Z) : z ∈ (chart c hc e hparameter a).target ↔ (c a, z) ∈ e.target := Iff.rfl

theorem total_value (a : P) {y : Y} (hy : y ∈ (chart c hc e hparameter a).source) :
    e (a, y) = (c a, chart c hc e hparameter a y) := Prod.ext (hparameter _ hy) rfl

end VeechDichotomy.ParameterSliceChart
