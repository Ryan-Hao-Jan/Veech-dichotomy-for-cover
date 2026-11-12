module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Compactness.Compact

/-! The compactness passage from marked bases through a proper map of cover
spaces. This is a general topology lemma, not a construction of Hurwitz
spaces and not a proof that the paper's particular map is proper.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

/-- The compact set `pr(R(P⁻¹(Φ(K × F))))` appearing in the proof. -/
theorem isCompact_cover_transport
    {A B Marked Cover Moduli : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Marked]
    [TopologicalSpace Cover] [TopologicalSpace Moduli]
    {K : Set A} {F : Set B} (hK : IsCompact K) (hF : IsCompact F)
    {Φ : A × B → Marked} (hΦ : Continuous Φ)
    {P : Cover → Marked} (hP : IsProperMap P)
    {R : Cover → Moduli} (hR : Continuous R) :
    IsCompact (R '' (P ⁻¹' (Φ '' (K ×ˢ F)))) :=
  (hP.isCompact_preimage ((hK.prod hF).image hΦ)).image hR

/-- Explicit sequence containment in that compact set. -/
theorem exists_compact_containing_cover_sequence
    {A B Marked Cover Moduli : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Marked]
    [TopologicalSpace Cover] [TopologicalSpace Moduli]
    {K : Set A} {F : Set B} (hK : IsCompact K) (hF : IsCompact F)
    {Φ : A × B → Marked} (hΦ : Continuous Φ)
    {P : Cover → Marked} (hP : IsProperMap P)
    {R : Cover → Moduli} (hR : Continuous R)
    (a : ℕ → A) (b : ℕ → B) (u : ℕ → Cover)
    (ha : ∀ n, a n ∈ K) (hb : ∀ n, b n ∈ F)
    (hu : ∀ n, P (u n) = Φ (a n, b n)) :
    ∃ C : Set Moduli, IsCompact C ∧ ∀ n, R (u n) ∈ C := by
  refine ⟨R '' (P ⁻¹' (Φ '' (K ×ˢ F))),
    isCompact_cover_transport hK hF hΦ hP hR, ?_⟩
  intro n
  refine mem_image_of_mem R ?_
  change P (u n) ∈ Φ '' (K ×ˢ F)
  rw [hu n]
  exact mem_image_of_mem Φ ⟨ha n, hb n⟩

end VeechDichotomy
