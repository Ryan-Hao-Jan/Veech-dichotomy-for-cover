module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Quot

/-! A finite set of invariants detecting equivalence bounds the number
of equivalence classes. Invariance on an entire equivalence class is not
required: choose one representative of each class and use detection. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteClassifyingMap

theorem finite_quotient {A B : Type*} [Finite B] (r : Setoid A) (f : A → B)
    (hdetect : ∀ a b, f a = f b → r.r a b) : Finite (Quotient r) := by
  classical
  let rep (c : Quotient r) := Classical.choose (Quotient.exists_rep c)
  have hrep (c : Quotient r) : Quotient.mk r (rep c) = c := Classical.choose_spec (Quotient.exists_rep c)
  apply Finite.of_injective (fun c : Quotient r => f (rep c))
  intro c d hcd
  exact (hrep c).symm.trans ((Quotient.sound (hdetect (rep c) (rep d) hcd)).trans (hrep d))

end VeechDichotomy.FiniteClassifyingMap
