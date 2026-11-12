module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section

/-!
# Deriving image-area preservation from proved local partial maps

A measurable set in a partial homeomorphism's source is partitioned into
countably many disjoint Borel pieces subordinate to a local cover. On
each piece the map agrees with one independently area-preserving local
partial homeomorphism. Injectivity makes the image pieces disjoint, so
countable additivity proves the global image-area equality.

Second countability supplies a countable subcover for an arbitrary open
family. No finiteness of the measure, or area-preservation premise for the
map being proved area preserving, is required.
-/

noncomputable section

namespace MNEC.LocalAreaGluing

open MeasureTheory Set Topology
open scoped ENNReal Classical

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measurableSet_image_of_subset_source (F : OpenPartialHomeomorph X X)
    (A : Set X) (hA : MeasurableSet A) (hsub : A ⊆ F.source) : MeasurableSet (F '' A) := by
  have himage : F '' A = (F.source.domRestrict F) '' (Subtype.val ⁻¹' A) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himage]
  exact F.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr
    (hA.preimage measurable_subtype_coe)

/-- Countably many verified local image-area identities imply the image
area identity of the actual injective partial map on its entire source. -/
theorem image_area_of_countable_cover (μ : Measure X) (F : OpenPartialHomeomorph X X)
    (U : ℕ → Set X) (E : ℕ → OpenPartialHomeomorph X X)
    (hU : ∀ n, MeasurableSet (U n)) (hcover : F.source ⊆ ⋃ n, U n)
    (hUsource : ∀ n, U n ⊆ (E n).source)
    (hagrees : ∀ n, EqOn F (E n) (U n))
    (hlocalArea : ∀ n (B : Set X), MeasurableSet B → B ⊆ (E n).source →
      μ (E n '' B) = μ B)
    (A : Set X) (hA : MeasurableSet A) (hAsource : A ⊆ F.source) :
    μ (F '' A) = μ A := by
  let C : ℕ → Set X := fun n => A ∩ U n
  let B : ℕ → Set X := disjointed C
  have hB : ∀ n, MeasurableSet (B n) := MeasurableSet.disjointed (fun n => hA.inter (hU n))
  have hBA (n : ℕ) : B n ⊆ A := (disjointed_subset C n).trans inter_subset_left
  have hBU (n : ℕ) : B n ⊆ U n := (disjointed_subset C n).trans inter_subset_right
  have hBF (n : ℕ) : B n ⊆ F.source := (hBA n).trans hAsource
  have hBunion : ⋃ n, B n = A := by
    rw [iUnion_disjointed]
    change (⋃ n, A ∩ U n) = A
    rw [← Set.inter_iUnion, inter_eq_left.mpr (hAsource.trans hcover)]
  have hBdisjoint : Pairwise (fun n m : ℕ => Disjoint (B n) (B m)) := disjoint_disjointed C
  have hImageMeas : ∀ n, MeasurableSet (F '' B n) :=
    fun n => measurableSet_image_of_subset_source F (B n) (hB n) (hBF n)
  have hImageDisjoint : Pairwise (fun n m : ℕ => Disjoint (F '' B n) (F '' B m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := F.injOn (hBF n hx) (hBF m hz) (hxy.trans hzy.symm)
    subst z
    exact Set.disjoint_left.mp (hBdisjoint hnm) hx hz
  have hAreaPiece (n : ℕ) : μ (F '' B n) = μ (B n) := by
    have himage : F '' B n = E n '' B n :=
      Set.image_congr fun x hx => hagrees n (hBU n hx)
    rw [himage]
    exact hlocalArea n (B n) (hB n) ((hBU n).trans (hUsource n))
  have hImageSum : μ (F '' A) = ∑' n : ℕ, μ (F '' B n) := by
    rw [← hBunion, Set.image_iUnion, measure_iUnion hImageDisjoint hImageMeas]
  have hSourceSum : μ A = ∑' n : ℕ, μ (B n) := by
    rw [← hBunion, measure_iUnion hBdisjoint hB]
  calc
    μ (F '' A) = ∑' n : ℕ, μ (F '' B n) := hImageSum
    _ = ∑' n : ℕ, μ (B n) := tsum_congr hAreaPiece
    _ = μ A := hSourceSum.symm

/-- An arbitrary open local cover suffices in a second-countable Borel
space: a countable subcover is derived, including the empty-family case. -/
theorem image_area_of_open_cover [SecondCountableTopology X]
    {ι : Type*} (μ : Measure X) (F : OpenPartialHomeomorph X X)
    (U : ι → Set X) (E : ι → OpenPartialHomeomorph X X)
    (hU : ∀ i, IsOpen (U i)) (hcover : F.source ⊆ ⋃ i, U i)
    (hUsource : ∀ i, U i ⊆ (E i).source)
    (hagrees : ∀ i, EqOn F (E i) (U i))
    (hlocalArea : ∀ i (B : Set X), MeasurableSet B → B ⊆ (E i).source →
      μ (E i '' B) = μ B)
    (A : Set X) (hA : MeasurableSet A) (hAsource : A ⊆ F.source) :
    μ (F '' A) = μ A := by
  by_cases hι : Nonempty ι
  · let _ := hι
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof F.source).indexed_countable_subcover
      U hU hcover
    exact image_area_of_countable_cover μ F (fun n => U (f n)) (fun n => E (f n))
      (fun n => (hU (f n)).measurableSet) hf (fun n => hUsource (f n))
      (fun n => hagrees (f n)) (fun n => hlocalArea (f n)) A hA hAsource
  · have hAempty : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcover (hAsource hx))
      exact hι ⟨i⟩
    rw [hAempty, Set.image_empty]

end MNEC.LocalAreaGluing
