module

public import VeechDichotomy.DirichletCornerSlopeOrder
public import Mathlib.Data.Finset.Sort

/-! Actual finite sets with injective real keys admit a literal increasing
enumeration. The order isomorphism of the finite real image supplies the
indices, and injectivity of the original keys proves the selected points
enumerate the entire original set exactly. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteRealKeyEnumeration

open Set

set_option backward.isDefEq.respectTransparency false

theorem enumerate_fin {α : Type*} (S : Finset α) (f : α → ℝ) (hf : InjOn f (S : Set α)) :
    ∃ v : Fin S.card → α, (∀ i, v i ∈ S) ∧ range v = (S : Set α) ∧ StrictMono (fun i => f (v i)) := by
  classical
  let W := S.image f
  have hcard : W.card = S.card := Finset.card_image_iff.mpr hf
  let e : Fin S.card ≃o W := W.orderIsoOfFin hcard
  have hex (t : W) : ∃ x : α, x ∈ S ∧ f x = t.val := Finset.mem_image.mp t.property
  let select : W → α := fun t => Classical.choose (hex t)
  have hselect (t : W) : select t ∈ S ∧ f (select t) = t.val := Classical.choose_spec (hex t)
  let v : Fin S.card → α := fun i => select (e i)
  have hmem (i : Fin S.card) : v i ∈ S := (hselect (e i)).1
  have hvalue (i : Fin S.card) : f (v i) = (e i).val := (hselect (e i)).2
  refine ⟨v, hmem, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact hmem i
    · intro x hx
      let t : W := ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      let i := e.symm t
      refine ⟨i, hf (hmem i) hx ?_⟩
      rw [hvalue]
      change (e (e.symm t)).val = f x
      rw [e.apply_symm_apply]
  · intro i j hij
    change f (v i) < f (v j)
    rw [hvalue, hvalue]
    exact e.strictMono hij

theorem enumerate {α : Type*} (S : Finset α) (f : α → ℝ) (hf : InjOn f (S : Set α)) (fallback : α) :
    ∃ v : ℕ → α, (∀ i : ℕ, i < S.card → v i ∈ S) ∧ v '' Iio S.card = (S : Set α) ∧
      (∀ i j : ℕ, i < j → j < S.card → f (v i) < f (v j)) := by
  classical
  obtain ⟨w, hmem, hrange, hstrict⟩ := enumerate_fin S f hf
  let v : ℕ → α := fun i => if hi : i < S.card then w ⟨i, hi⟩ else fallback
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [v, dite_eq_left hi] using! hmem ⟨i, hi⟩
  · apply Subset.antisymm
    · rintro _ ⟨i, hi, rfl⟩
      have hi' : i < S.card := hi
      simpa only [v, dite_eq_left hi'] using! hmem ⟨i, hi'⟩
    · intro x hx
      have hx' : x ∈ range w := by rw [hrange]; exact hx
      obtain ⟨i, hi⟩ := hx'
      refine ⟨i.val, i.isLt, ?_⟩
      simpa only [v, dite_eq_left i.isLt] using! hi
  · intro i j hij hj
    have hi : i < S.card := hij.trans hj
    simpa only [v, dite_eq_left hi, dite_eq_left hj] using!
      hstrict (show (⟨i, hi⟩ : Fin S.card) < ⟨j, hj⟩ from hij)

end VeechDichotomy.FiniteRealKeyEnumeration
