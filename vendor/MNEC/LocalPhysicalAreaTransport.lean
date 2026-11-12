module

public import MNEC.RegularCoordinateArea
public import MNEC.RegularCountability
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic.Choose

@[expose] public section

/-!
# Area transport between different actual regular surfaces

Countable gluing transfers verified local image-measure identities between
different spaces. Actual physical chart translations satisfy these local
identities by the two independently proved chart-area formulas. The final
criterion requires geometric chart factorizations, and does not assert
that a particular surgery map satisfies those hypotheses.
-/

noncomputable section

namespace MNEC.LocalPhysicalAreaTransport

open MeasureTheory Set Topology
open scoped ENNReal Classical

section General

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem measurableSet_image_of_subset_source (F : OpenPartialHomeomorph X Y)
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

theorem image_area_of_countable_cover (μ : Measure X) (ν : Measure Y) (F : OpenPartialHomeomorph X Y)
    (U : ℕ → Set X) (E : ℕ → OpenPartialHomeomorph X Y)
    (hU : ∀ n, MeasurableSet (U n)) (hcover : F.source ⊆ ⋃ n, U n)
    (hUsource : ∀ n, U n ⊆ (E n).source) (hagrees : ∀ n, EqOn F (E n) (U n))
    (hlocalArea : ∀ n (B : Set X), MeasurableSet B → B ⊆ (E n).source → ν (E n '' B) = μ B)
    (A : Set X) (hA : MeasurableSet A) (hAsource : A ⊆ F.source) : ν (F '' A) = μ A := by
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
  have hAreaPiece (n : ℕ) : ν (F '' B n) = μ (B n) := by
    have himage : F '' B n = E n '' B n := Set.image_congr fun x hx => hagrees n (hBU n hx)
    rw [himage]
    exact hlocalArea n (B n) (hB n) ((hBU n).trans (hUsource n))
  have hImageSum : ν (F '' A) = ∑' n : ℕ, ν (F '' B n) := by
    rw [← hBunion, Set.image_iUnion, measure_iUnion hImageDisjoint hImageMeas]
  have hSourceSum : μ A = ∑' n : ℕ, μ (B n) := by
    rw [← hBunion, measure_iUnion hBdisjoint hB]
  calc
    ν (F '' A) = ∑' n : ℕ, ν (F '' B n) := hImageSum
    _ = ∑' n : ℕ, μ (B n) := tsum_congr hAreaPiece
    _ = μ A := hSourceSum.symm

theorem image_area_of_open_cover [SecondCountableTopology X] {ι : Type*}
    (μ : Measure X) (ν : Measure Y) (F : OpenPartialHomeomorph X Y)
    (U : ι → Set X) (E : ι → OpenPartialHomeomorph X Y)
    (hU : ∀ i, IsOpen (U i)) (hcover : F.source ⊆ ⋃ i, U i)
    (hUsource : ∀ i, U i ⊆ (E i).source) (hagrees : ∀ i, EqOn F (E i) (U i))
    (hlocalArea : ∀ i (B : Set X), MeasurableSet B → B ⊆ (E i).source → ν (E i '' B) = μ B)
    (A : Set X) (hA : MeasurableSet A) (hAsource : A ⊆ F.source) : ν (F '' A) = μ A := by
  by_cases hι : Nonempty ι
  · let _ := hι
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof F.source).indexed_countable_subcover U hU hcover
    exact image_area_of_countable_cover μ ν F (fun n => U (f n)) (fun n => E (f n))
      (fun n => (hU (f n)).measurableSet) hf (fun n => hUsource (f n))
      (fun n => hagrees (f n)) (fun n => hlocalArea (f n)) A hA hAsource
  · have hAempty : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcover (hAsource hx))
      exact hι ⟨i⟩
    simp only [hAempty, Set.image_empty, measure_empty]

end General

open LatticeTorus RegularChartedSpace RegularAtlasCoverage RegularTopologyArea RegularCoordinateArea

section TwoCharts

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def chartTranslation (e : OpenPartialHomeomorph Plane X) (d : OpenPartialHomeomorph Plane Y) (c : Plane) :
    OpenPartialHomeomorph X Y := (e.symm.transHomeomorph (Homeomorph.addRight c)).trans d

theorem chartTranslation_apply (e : OpenPartialHomeomorph Plane X) (d : OpenPartialHomeomorph Plane Y)
    (c : Plane) (x : X) : chartTranslation e d c x = d (e.symm x + c) := rfl

theorem mem_chartTranslation_source (e : OpenPartialHomeomorph Plane X) (d : OpenPartialHomeomorph Plane Y)
    (c : Plane) (x : X) : x ∈ (chartTranslation e d c).source ↔ x ∈ e.target ∧ e.symm x + c ∈ d.source := Iff.rfl

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]

theorem chartTranslation_image_area (μ : Measure X) (ν : Measure Y)
    (e : OpenPartialHomeomorph Plane X) (d : OpenPartialHomeomorph Plane Y)
    (he : ∀ V : Set Plane, MeasurableSet V → V ⊆ e.source → μ (e '' V) = volume V)
    (hd : ∀ V : Set Plane, MeasurableSet V → V ⊆ d.source → ν (d '' V) = volume V)
    (c : Plane) (V : Set X) (hV : MeasurableSet V) (hsub : V ⊆ (chartTranslation e d c).source) :
    ν (chartTranslation e d c '' V) = μ V := by
  let B : Set Plane := e.symm '' V
  let D : Set Plane := (fun p : Plane => p + c) '' B
  have htarget : V ⊆ e.target := fun x hx => ((mem_chartTranslation_source e d c x).mp (hsub hx)).1
  have hB : MeasurableSet B := measurableSet_image_of_subset_source e.symm V hV htarget
  have hBsource : B ⊆ e.source := by
    rintro p ⟨x, hx, rfl⟩
    exact e.map_target (htarget hx)
  have hD : MeasurableSet D := measurableSet_image_of_subset_source
    (Homeomorph.addRight c).toOpenPartialHomeomorph B hB (subset_univ _)
  have hDsource : D ⊆ d.source := by
    rintro p ⟨b, ⟨x, hx, hxb⟩, rfl⟩
    rw [← hxb]
    exact ((mem_chartTranslation_source e d c x).mp (hsub hx)).2
  have himage : chartTranslation e d c '' V = d '' D := by
    change (fun x => d (e.symm x + c)) '' V = d '' ((fun p : Plane => p + c) '' (e.symm '' V))
    rw [Set.image_image, Set.image_image]
  have hinverse : e '' B = V := e.image_symm_image_of_subset_target htarget
  calc
    ν (chartTranslation e d c '' V) = ν (d '' D) := congrArg ν himage
    _ = volume D := hd D hD hDsource
    _ = volume B := LocalDirectionalArea.volume_translation c B
    _ = μ (e '' B) := (he B hB hBsource).symm
    _ = μ V := congrArg μ hinverse

end TwoCharts

section ActualRegular

variable {L₁ L₂ M₁ M₂ : Lattice} {w z : Plane}

def regularTranslation (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane) :
    OpenPartialHomeomorph (Regular M₁ M₂ z) (Regular L₁ L₂ w) :=
  chartTranslation (regularModel hwM₁ hwM₂ i) (regularModel hwL₁ hwL₂ j) c

theorem regularTranslation_apply (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane) (x : Regular M₁ M₂ z) :
    regularTranslation hwM₁ hwM₂ hwL₁ hwL₂ i j c x =
      (regularChart hwL₁ hwL₂ j).symm (regularChart hwM₁ hwM₂ i x + c) := rfl

theorem mem_regularTranslation_source (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane) (x : Regular M₁ M₂ z) :
    x ∈ (regularTranslation hwM₁ hwM₂ hwL₁ hwL₂ i j c).source ↔
      x ∈ (regularChart hwM₁ hwM₂ i).source ∧
        regularChart hwM₁ hwM₂ i x + c ∈ (regularChart hwL₁ hwL₂ j).target := Iff.rfl

theorem regularTranslation_image_area (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane) (V : Set (Regular M₁ M₂ z))
    (hV : MeasurableSet V) (hsub : V ⊆ (regularTranslation hwM₁ hwM₂ hwL₁ hwL₂ i j c).source) :
    regularArea L₁ L₂ w (regularTranslation hwM₁ hwM₂ hwL₁ hwL₂ i j c '' V) = regularArea M₁ M₂ z V :=
  chartTranslation_image_area (regularArea M₁ M₂ z) (regularArea L₁ L₂ w)
    (regularModel hwM₁ hwM₂ i) (regularModel hwL₁ hwL₂ j)
    (regularModel_area_image hwM₁ hwM₂ i) (regularModel_area_image hwL₁ hwL₂ j) c V hV hsub

theorem homeomorph_image_area_of_local_formulas
    (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (f : Regular M₁ M₂ z ≃ₜ Regular L₁ L₂ w)
    (hlocal : ∀ x : Regular M₁ M₂ z, ∃ (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane),
      x ∈ (regularChart hwM₁ hwM₂ i).source ∧
      regularChart hwM₁ hwM₂ i x + c ∈ (regularChart hwL₁ hwL₂ j).target ∧
      ∀ᶠ y in 𝓝 x, f y = (regularChart hwL₁ hwL₂ j).symm (regularChart hwM₁ hwM₂ i y + c))
    (A : Set (Regular M₁ M₂ z)) (hA : MeasurableSet A) :
    regularArea L₁ L₂ w (f '' A) = regularArea M₁ M₂ z A := by
  let : SecondCountableTopology (Regular M₁ M₂ z) := RegularCountability.secondCountableRegular hwM₁ hwM₂
  have hdata : ∀ x : Regular M₁ M₂ z,
      ∃ (E : OpenPartialHomeomorph (Regular M₁ M₂ z) (Regular L₁ L₂ w)) (U : Set (Regular M₁ M₂ z)),
        IsOpen U ∧ x ∈ U ∧ U ⊆ E.source ∧ EqOn f E U ∧
          ∀ B, MeasurableSet B → B ⊆ E.source → regularArea L₁ L₂ w (E '' B) = regularArea M₁ M₂ z B := by
    intro x
    obtain ⟨i, j, c, hx, hy, hg⟩ := hlocal x
    let E := regularTranslation hwM₁ hwM₂ hwL₁ hwL₂ i j c
    have hxE : x ∈ E.source := (mem_regularTranslation_source hwM₁ hwM₂ hwL₁ hwL₂ i j c x).mpr ⟨hx, hy⟩
    have hAgree : ∀ᶠ y in 𝓝 x, f y = E y := by
      simpa only [E, regularTranslation_apply] using hg
    have hBoth : ∀ᶠ y in 𝓝 x, y ∈ E.source ∧ f y = E y := by
      filter_upwards [E.open_source.mem_nhds (x := x) hxE, hAgree] with y hyE hyEq
      exact ⟨hyE, hyEq⟩
    obtain ⟨U, hUp, hU, hxU⟩ := eventually_nhds_iff.mp hBoth
    refine ⟨E, U, hU, hxU, (fun y hyU => (hUp y hyU).1), (fun y hyU => (hUp y hyU).2), ?_⟩
    intro B hB hBE
    exact regularTranslation_image_area hwM₁ hwM₂ hwL₁ hwL₂ i j c B hB hBE
  choose E U hU hxU hUs hEq hArea using hdata
  let F := f.toOpenPartialHomeomorph
  have hcover : F.source ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  change regularArea L₁ L₂ w (F '' A) = regularArea M₁ M₂ z A
  exact image_area_of_open_cover (regularArea M₁ M₂ z) (regularArea L₁ L₂ w) F U E hU hcover hUs
    (fun x y hy => by change f y = E x y; exact hEq x hy) hArea A hA (subset_univ _)

theorem measurePreserving_of_local_formulas
    (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (f : Regular M₁ M₂ z ≃ₜ Regular L₁ L₂ w)
    (hlocal : ∀ x : Regular M₁ M₂ z, ∃ (i : Index M₁ M₂ z) (j : Index L₁ L₂ w) (c : Plane),
      x ∈ (regularChart hwM₁ hwM₂ i).source ∧
      regularChart hwM₁ hwM₂ i x + c ∈ (regularChart hwL₁ hwL₂ j).target ∧
      ∀ᶠ y in 𝓝 x, f y = (regularChart hwL₁ hwL₂ j).symm (regularChart hwM₁ hwM₂ i y + c)) :
    MeasurePreserving f (regularArea M₁ M₂ z) (regularArea L₁ L₂ w) where
  measurable := f.measurable
  map_eq := by
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply f.measurable hB]
    have h := homeomorph_image_area_of_local_formulas hwM₁ hwM₂ hwL₁ hwL₂ f hlocal
      (f ⁻¹' B) (hB.preimage f.measurable)
    rw [Set.image_preimage_eq B f.surjective] at h
    exact h.symm

theorem surface_measurePreserving_of_regular
    (hwM₁ : M₁.EmbeddedSlit z) (hwM₂ : M₂.EmbeddedSlit z)
    (hwL₁ : L₁.EmbeddedSlit w) (hwL₂ : L₂.EmbeddedSlit w)
    (F : SlitConnectedSum.Surface M₁ M₂ z ≃ₜ SlitConnectedSum.Surface L₁ L₂ w)
    (f : Regular M₁ M₂ z ≃ₜ Regular L₁ L₂ w)
    (hvalue : ∀ x : Regular M₁ M₂ z, (f x).val = F x.val)
    (hMP : MeasurePreserving f (regularArea M₁ M₂ z) (regularArea L₁ L₂ w)) :
    MeasurePreserving F (ConnectedSumArea.area M₁ M₂ z) (ConnectedSumArea.area L₁ L₂ w) where
  measurable := F.measurable
  map_eq := by
    have hS := regular_inclusion_measurePreserving M₁ M₂ z hwM₁ hwM₂
    have hT := regular_inclusion_measurePreserving L₁ L₂ w hwL₁ hwL₂
    rw [← hS.map_eq, Measure.map_map F.measurable measurable_subtype_coe]
    have hcomp : F ∘ (Subtype.val : Regular M₁ M₂ z → SlitConnectedSum.Surface M₁ M₂ z) =
        (Subtype.val : Regular L₁ L₂ w → SlitConnectedSum.Surface L₁ L₂ w) ∘ f := by
      funext x
      exact (hvalue x).symm
    rw [hcomp, ← Measure.map_map measurable_subtype_coe f.measurable, hMP.map_eq, hT.map_eq]

end ActualRegular

end MNEC.LocalPhysicalAreaTransport

