module

public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! The finite-monodromy argument used when lifting a periodic base leaf.
The hypotheses refer to actual maps and their iterates. No statement
about minimality of translation surfaces is supplied as a hypothesis.
-/

@[expose] public section

open Set Function

namespace VeechDichotomy

/-- A periodic point downstairs has periodic lifts under an injective
time map, provided its fiber is finite. -/
theorem periodic_lift_of_finite_fiber
    {X Y : Type*} {f : Y → Y} {g : X → X} {π : Y → X}
    (hf : Function.Injective f) (hπ : Function.Semiconj π f g)
    {y : Y} (hfinite : (π ⁻¹' {π y}).Finite)
    {n : ℕ} (hn : 0 < n) (hy : Function.IsPeriodicPt g n (π y)) :
    ∃ k : ℕ, 0 < k ∧ Function.IsPeriodicPt f k y := by
  let S := π ⁻¹' {π y}
  let : Finite S := hfinite.to_subtype
  let r : S → S := fun z => ⟨f^[n] z, by
    change π (f^[n] z) = π y
    rw [(hπ.iterate_right n) z, z.property]
    exact hy⟩
  have hr : Injective r := by
    intro x z hxz
    apply Subtype.ext
    exact hf.iterate n (congrArg Subtype.val hxz)
  have hval : Semiconj (Subtype.val : S → Y) r (f^[n]) := fun _ => rfl
  obtain ⟨k, hk, hky⟩ := hr.mem_periodicPts (⟨y, rfl⟩ : S)
  refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
  have h := hky.map hval
  simpa only [IsPeriodicPt, iterate_mul] using h

end VeechDichotomy
