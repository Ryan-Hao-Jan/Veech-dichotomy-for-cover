module

public import Mathlib.Topology.Homotopy.Lifting

/-! Connected ordinary covers have transitive actual monodromy on their
fibers. The proof projects a path in the covering space and uses unique
homotopy lifting. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CoverMonodromy

set_option backward.isDefEq.respectTransparency false

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (cov : IsCoveringMap p)

theorem transitive [PathConnectedSpace E] (x : X) (a b : p ⁻¹' {x}) :
    ∃ γ : FundamentalGroup X x, cov.monodromyPerm x γ a = b := by
  let Γ : Path.Homotopic.Quotient a.val b.val :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a.val b.val)
  let γ : Path.Homotopic.Quotient x x :=
    (Γ.map ⟨p, cov.continuous⟩).cast a.property.symm b.property.symm
  refine ⟨.of γ, ?_⟩
  change cov.monodromy γ a = b
  apply cov.monodromy_eq_of_map_eq Γ
  exact ((Path.Homotopic.Quotient.cast_cast (Γ.map ⟨p, cov.continuous⟩)
    a.property.symm b.property.symm a.property b.property).trans
      (Path.Homotopic.Quotient.cast_rfl_rfl _)).symm

end VeechDichotomy.CoverMonodromy
