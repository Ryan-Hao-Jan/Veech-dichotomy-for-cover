module

public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Quot

/-! Finitely many quotient classes admit finitely many actual representatives.
The statement also covers an empty underlying family. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteClassRepresentatives

theorem exists_representatives {A : Type*} (r : Setoid A) [Finite (Quotient r)] :
    ∃ J : Set A, J.Finite ∧ ∀ a, ∃ b ∈ J, r.r a b := by
  refine ⟨Set.range (Quotient.out : Quotient r → A), Set.finite_range _, ?_⟩
  intro a
  refine ⟨(Quotient.mk r a).out, ⟨Quotient.mk r a, rfl⟩, ?_⟩
  exact r.symm (Quotient.mk_out a)

end VeechDichotomy.FiniteClassRepresentatives
