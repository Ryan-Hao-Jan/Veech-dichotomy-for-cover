module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! The algebraic finiteness used in the Hurwitz argument: homomorphisms
from a finitely generated group to a finite group are determined by finitely
many values. Finite generation of a native punctured curve's fundamental
group is a separate topological theorem and is not postulated here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteMonodromyRepresentations

theorem finite_homs_of_fg {G H : Type*} [Group G] [Group H] [Finite H]
    (hG : Group.FG G) : Finite (G →* H) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp hG
  let : Finite S := hfin.to_subtype
  apply Finite.of_injective (fun f : G →* H => fun s : S => f s.val)
  intro f g heq
  apply MonoidHom.eq_of_eqOn_dense hS
  intro s hs
  exact congrFun heq ⟨s, hs⟩

end VeechDichotomy.FiniteMonodromyRepresentations
