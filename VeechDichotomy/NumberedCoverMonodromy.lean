module

public import VeechDichotomy.CoverMonodromyClassification

/-! Equality of actual monodromy representations after labeling their
fibers produces an equivariant fiber bijection, and hence a cover isomorphism.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NumberedCoverMonodromy

open Set

set_option backward.isDefEq.respectTransparency false

variable {E F X L : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} (cp : IsCoveringMap p) (cq : IsCoveringMap q) {x : X}

def representation (α : (p ⁻¹' {x}) ≃ L) : FundamentalGroup X x →* Equiv.Perm L :=
  α.permCongrHom.toMonoidHom.comp (cp.monodromyPerm x)

theorem equivariant_of_eq (α : (p ⁻¹' {x}) ≃ L) (β : (q ⁻¹' {x}) ≃ L)
    (heq : representation cp α = representation cq β) :
    CoverMonodromyClassification.Equivariant cp cq (α.trans β.symm) := by
  intro γ a
  apply β.injective
  have h := congrArg (fun r : FundamentalGroup X x →* Equiv.Perm L => r γ (α a)) heq
  change α (cp.monodromyPerm x γ (α.symm (α a))) =
    β (cq.monodromyPerm x γ (β.symm (α a))) at h
  rw [Equiv.symm_apply_apply] at h
  change β (β.symm (α (cp.monodromyPerm x γ a))) =
    β (cq.monodromyPerm x γ (β.symm (α a)))
  rw [Equiv.apply_symm_apply]
  exact h

end VeechDichotomy.NumberedCoverMonodromy
