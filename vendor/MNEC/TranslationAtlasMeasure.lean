module

public import MNEC.TranslationVolume
public import MNEC.LocalPhysicalAreaTransport
public import MNEC.ChartAreaSupport
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Support

/-! Canonical Euclidean measure of a genuine translation atlas. A countable
chart cover is derived from SCT; measurable disjoint atoms subordinate to
that cover assemble actual pullback Lebesgue measures. Compatibility is
proved by local translation volume invariance. The resulting measure has
every chart formula and is unique, independently of the chosen cover. -/

@[expose] public section
noncomputable section
namespace MNEC.TranslationAtlasMeasure

open LatticeTorus TranslationGroupoid MeasureTheory Set Topology
open scoped ENNReal Classical
variable {M I : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

def chartMeasure (e : OpenPartialHomeomorph M Plane) : Measure M :=
  ((volume : Measure Plane).comap (e.source.domRestrict e)).map (Subtype.val : e.source → M)

theorem chartMeasure_apply (e : OpenPartialHomeomorph M Plane) (A : Set M) :
    chartMeasure e A = volume (e '' (A ∩ e.source)) := by
  rw [chartMeasure, (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).map_apply,
    e.isOpenEmbedding_restrict.measurableEmbedding.comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
  · rintro ⟨x, ⟨hxA, hxE⟩, rfl⟩
    exact ⟨⟨x, hxE⟩, hxA, rfl⟩

structure Cover (c : I → OpenPartialHomeomorph M Plane) where
  index : ℕ → I
  cover : ⋃ n : ℕ, (c (index n)).source = univ

omit [MeasurableSpace M] [BorelSpace M] in
theorem exists_cover [SecondCountableTopology M] [Nonempty I]
    (c : I → OpenPartialHomeomorph M Plane) (hcover : ∀ x : M, ∃ i, x ∈ (c i).source) : Nonempty (Cover c) := by
  have hsub : (univ : Set M) ⊆ ⋃ i, (c i).source := by
    intro x _
    exact mem_iUnion.mpr (hcover x)
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof (univ : Set M)).indexed_countable_subcover
    (fun i => (c i).source) (fun i => (c i).open_source) hsub
  exact ⟨⟨f, eq_univ_of_forall (fun x => hf (mem_univ x))⟩⟩

def atom (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) (n : ℕ) : Set M :=
  disjointed (fun k : ℕ => (c (C.index k)).source) n

theorem atom_measurable (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) (n : ℕ) : MeasurableSet (atom c C n) :=
  MeasurableSet.disjointed (fun k => (c (C.index k)).open_source.measurableSet) n

omit [MeasurableSpace M] [BorelSpace M] in
theorem atom_subset (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) (n : ℕ) :
    atom c C n ⊆ (c (C.index n)).source := disjointed_subset _ n

omit [MeasurableSpace M] [BorelSpace M] in
theorem atom_disjoint (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) :
    Pairwise (fun n k : ℕ => Disjoint (atom c C n) (atom c C k)) := disjoint_disjointed _

omit [MeasurableSpace M] [BorelSpace M] in
theorem atom_union (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) : ⋃ n : ℕ, atom c C n = univ := by
  change (⋃ n : ℕ, disjointed (fun k : ℕ => (c (C.index k)).source) n) = univ
  rw [iUnion_disjointed]
  exact C.cover

def area (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) : Measure M :=
  Measure.sum (fun n : ℕ => (chartMeasure (c (C.index n))).restrict (atom c C n))

theorem area_apply (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) (A : Set M) :
    area c C A = ∑' n : ℕ, volume (c (C.index n) '' (A ∩ atom c C n)) := by
  rw [area, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro n
  rw [Measure.restrict_apply' (atom_measurable c C n), chartMeasure_apply,
    inter_eq_left.mpr (inter_subset_right.trans (atom_subset c C n))]

/-- Actual overlap compatibility comes from derived local translations,
not a measure-preservation certificate. -/
theorem overlap_volume (e f : OpenPartialHomeomorph M Plane)
    (htrans : LocallyTranslationOn (e.symm.trans f) (e.symm.trans f).source)
    (A : Set M) (hA : MeasurableSet A) (he : A ⊆ e.source) (hf : A ⊆ f.source) :
    volume (f '' A) = volume (e '' A) := by
  have hB : MeasurableSet (e '' A) := LocalPhysicalAreaTransport.measurableSet_image_of_subset_source e A hA he
  have hsub : e '' A ⊆ (e.symm.trans f).source := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨e.map_source (he hx), ?_⟩
    change e.symm (e x) ∈ f.source
    rw [e.left_inv (he hx)]
    exact hf hx
  have himage : (e.symm.trans f) '' (e '' A) = f '' A := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by change f x = f (e.symm (e x)); rw [e.left_inv (he hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, by change f (e.symm (e x)) = f x; rw [e.left_inv (he hx)]⟩
  rw [← himage]
  exact TranslationVolume.image_volume (e.symm.trans f) htrans (e '' A) hB hsub

/-- The assembled measure has the exact formula in ANY compatible test
chart, including charts outside the selected countable subcover. -/
theorem area_in_chart (c : I → OpenPartialHomeomorph M Plane) (C : Cover c)
    (e : OpenPartialHomeomorph M Plane)
    (hcompat : ∀ i, LocallyTranslationOn ((c i).symm.trans e) ((c i).symm.trans e).source)
    (A : Set M) (hA : MeasurableSet A) (hsub : A ⊆ e.source) : area c C A = volume (e '' A) := by
  let B : ℕ → Set M := fun n => A ∩ atom c C n
  have hB : ∀ n, MeasurableSet (B n) := fun n => hA.inter (atom_measurable c C n)
  have hBe : ∀ n, B n ⊆ e.source := fun n => inter_subset_left.trans hsub
  have hBi : ∀ n, B n ⊆ (c (C.index n)).source := fun n => inter_subset_right.trans (atom_subset c C n)
  have hBunion : ⋃ n : ℕ, B n = A := by
    change (⋃ n : ℕ, A ∩ atom c C n) = A
    rw [← inter_iUnion, atom_union, inter_univ]
  have hBdisj : Pairwise (fun n k : ℕ => Disjoint (B n) (B k)) := by
    intro n k hnk
    exact (atom_disjoint c C hnk).mono inter_subset_right inter_subset_right
  have hImageMeas : ∀ n, MeasurableSet (e '' B n) := fun n =>
    LocalPhysicalAreaTransport.measurableSet_image_of_subset_source e (B n) (hB n) (hBe n)
  have hImageDisj : Pairwise (fun n k : ℕ => Disjoint (e '' B n) (e '' B k)) := by
    intro n k hnk
    apply disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := e.injOn (hBe n hx) (hBe k hz) (hxy.trans hzy.symm)
    subst z
    exact disjoint_left.mp (hBdisj hnk) hx hz
  calc
    area c C A = ∑' n : ℕ, volume (c (C.index n) '' B n) := area_apply c C A
    _ = ∑' n : ℕ, volume (e '' B n) := tsum_congr (fun n =>
      (overlap_volume (c (C.index n)) e (hcompat (C.index n)) (B n) (hB n) (hBi n) (hBe n)).symm)
    _ = volume (e '' A) := by rw [← hBunion, image_iUnion, measure_iUnion hImageDisj hImageMeas]

theorem area_chart_formula (c : I → OpenPartialHomeomorph M Plane) (C : Cover c)
    (hcompat : ∀ i j, LocallyTranslationOn ((c i).symm.trans (c j)) ((c i).symm.trans (c j)).source)
    (i : I) (A : Set M) (hA : MeasurableSet A) (hsub : A ⊆ (c i).source) :
    area c C A = volume (c i '' A) := area_in_chart c C (c i) (fun j => hcompat j i) A hA hsub

theorem area_inverse_chart_formula (c : I → OpenPartialHomeomorph M Plane) (C : Cover c)
    (hcompat : ∀ i j, LocallyTranslationOn ((c i).symm.trans (c j)) ((c i).symm.trans (c j)).source)
    (i : I) (B : Set Plane) (hB : MeasurableSet B) (hsub : B ⊆ (c i).target) :
    area c C ((c i).symm '' B) = volume B := by
  have hA := LocalPhysicalAreaTransport.measurableSet_image_of_subset_source (c i).symm B hB hsub
  have hAsub : (c i).symm '' B ⊆ (c i).source := by rintro _ ⟨p, hp, rfl⟩; exact (c i).map_target (hsub hp)
  rw [area_chart_formula c C hcompat i _ hA hAsub]
  have hInv : c i '' ((c i).symm '' B) = B := (c i).image_symm_image_of_subset_target hsub
  exact congrArg volume hInv

/-- The chart identities determine the measure uniquely, with no finite
mass or sigma-finite hypothesis. -/
theorem unique (c : I → OpenPartialHomeomorph M Plane) (C : Cover c) (ν : Measure M)
    (hν : ∀ i (A : Set M), MeasurableSet A → A ⊆ (c i).source → ν A = volume (c i '' A)) : ν = area c C := by
  apply Measure.ext
  intro A hA
  have hB : ∀ n, MeasurableSet (A ∩ atom c C n) := fun n => hA.inter (atom_measurable c C n)
  have hdisj : Pairwise (fun n k : ℕ => Disjoint (A ∩ atom c C n) (A ∩ atom c C k)) := by
    intro n k hnk
    exact (atom_disjoint c C hnk).mono inter_subset_right inter_subset_right
  have hunion : ⋃ n : ℕ, A ∩ atom c C n = A := by rw [← inter_iUnion, atom_union, inter_univ]
  calc
    ν A = ∑' n : ℕ, ν (A ∩ atom c C n) := by
      calc
        ν A = ν (⋃ n : ℕ, A ∩ atom c C n) := congrArg ν hunion.symm
        _ = ∑' n : ℕ, ν (A ∩ atom c C n) := measure_iUnion hdisj hB
    _ = ∑' n : ℕ, volume (c (C.index n) '' (A ∩ atom c C n)) :=
      tsum_congr (fun n => hν (C.index n) _ (hB n) (inter_subset_right.trans (atom_subset c C n)))
    _ = area c C A := (area_apply c C A).symm

theorem cover_independent (c : I → OpenPartialHomeomorph M Plane)
    (hcompat : ∀ i j, LocallyTranslationOn ((c i).symm.trans (c j)) ((c i).symm.trans (c j)).source)
    (C D : Cover c) : area c C = area c D :=
  (unique c C (area c D) (fun i A hA hsub => area_chart_formula c D hcompat i A hA hsub)).symm

theorem area_isOpenPosMeasure (c : I → OpenPartialHomeomorph M Plane) (C : Cover c)
    (hcompat : ∀ i j, LocallyTranslationOn ((c i).symm.trans (c j)) ((c i).symm.trans (c j)).source) :
    Measure.IsOpenPosMeasure (area c C) := by
  apply ChartAreaSupport.isOpenPosMeasure_of_chart_area (area c C) (fun i => (c i).symm)
  · intro x
    have hx : x ∈ ⋃ n : ℕ, (c (C.index n)).source := by rw [C.cover]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨C.index n, hn⟩
  · exact area_inverse_chart_formula c C hcompat

theorem area_support_eq_univ (c : I → OpenPartialHomeomorph M Plane) (C : Cover c)
    (hcompat : ∀ i j, LocallyTranslationOn ((c i).symm.trans (c j)) ((c i).symm.trans (c j)).source) :
    (area c C).support = univ := by
  let : Measure.IsOpenPosMeasure (area c C) := area_isOpenPosMeasure c C hcompat
  exact Measure.support_eq_univ

end MNEC.TranslationAtlasMeasure
