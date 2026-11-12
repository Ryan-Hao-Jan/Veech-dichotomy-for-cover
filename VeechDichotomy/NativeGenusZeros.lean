module

public import VeechDichotomy.NativeFormRatios
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! Every actual native differential on a compact curve of genus at
least two has a zero. A nowhere-zero differential would make every other
form a constant scalar multiple by compact holomorphic Liouville, so the
actual holomorphic-form space would have dimension at most one.
No canonical-degree or Riemann--Roch oracle is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeGenusZeros

open MNEC.NativeAbelianDifferential Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem all_forms_proportional (hno : ∀ y : X, q.val.toFun y ≠ 0) (η : Jacobians.HolomorphicOneForms X) :
    ∃ c : ℂ, η = c • q.val := by
  obtain ⟨c, hc⟩ := (NativeFormRatios.mdifferentiable q η hno).exists_eq_const_of_compactSpace
  refine ⟨c, ?_⟩
  apply ContMDiffSection.ext
  intro y
  apply ContinuousLinearMap.ext
  intro v
  have hpoint := NativeFormRatios.pointwise_smul q η y (hno y)
  have hr : NativeFormRatios.ratio q η y = c := congrFun hc y
  rw [hr] at hpoint
  exact congrArg (fun L => L v) hpoint

theorem genus_le_one_of_no_zeros (hno : ∀ y : X, q.val.toFun y ≠ 0) : genus X ≤ 1 := by
  apply finrank_le_one q.val
  intro η
  obtain ⟨c, hc⟩ := all_forms_proportional q hno η
  exact ⟨c, hc.symm⟩

theorem zeroSet_nonempty (hgenus : 2 ≤ genus X) : (zeroSet q).Nonempty := by
  by_contra hnone
  have hno : ∀ y : X, q.val.toFun y ≠ 0 := fun y hy => hnone ⟨y, hy⟩
  have hle := genus_le_one_of_no_zeros q hno
  exact Nat.not_succ_le_self 1 (hgenus.trans hle)

end VeechDichotomy.NativeGenusZeros
