module

public import MNEC.NativePrimitiveAreaCharts
public import MNEC.TranslationAtlasMeasure

/-! Canonical physical area of an arbitrary genuine native holomorphic
form on its regular locus. Countable disjoint patch assembly constructs
the measure. ALL genuine primitive charts have proved Lebesgue formulas;
uniqueness makes it independent of every gluing/primitive-cover choice.
Finite total mass, AE completeness and normalization are not claimed. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeRegularArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativePrimitiveAreaCharts MeasureTheory Set Topology
open scoped ENNReal Classical Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/- Canonical original-curve Borel sigma algebra, with its induced regular
subtype sigma algebra. No measurable-space certificate is an input. -/
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def selectedCover (q : Differential X) : TranslationAtlasMeasure.Cover (chart q) := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  let : Nonempty (Index q) := index_nonempty q
  exact Classical.choice (TranslationAtlasMeasure.exists_cover (chart q) (covers q))

def regularArea (q : Differential X) : Measure (Regular q) :=
  TranslationAtlasMeasure.area (chart q) (selectedCover q)

/-- Every ACTUAL primitive chart has its exact physical Lebesgue formula,
not merely those occurring in the selected countable subcover. -/
theorem primitive_chart_formula (q : Differential X) (i : Index q) (A : Set (Regular q))
    (hA : MeasurableSet A) (hsub : A ⊆ (chart q i).source) :
    regularArea q A = volume (chart q i '' A) :=
  TranslationAtlasMeasure.area_chart_formula (chart q) (selectedCover q)
    (NativePrimitiveAreaCharts.transition_locally_translation q) i A hA hsub

theorem primitive_chart_image (q : Differential X) (i : Index q) (B : Set Plane)
    (hB : MeasurableSet B) (hsub : B ⊆ (chart q i).target) :
    regularArea q ((chart q i).symm '' B) = volume B :=
  TranslationAtlasMeasure.area_inverse_chart_formula (chart q) (selectedCover q)
    (NativePrimitiveAreaCharts.transition_locally_translation q) i B hB hsub

theorem coordinateChart_formula (q : Differential X) (i : Regular q) (A : Set (Regular q))
    (hA : MeasurableSet A) (hsub : A ⊆ (coordinateChart q i).source) :
    regularArea q A = volume (coordinateChart q i '' A) := by
  have h := primitive_chart_formula q (selectedIndex q i) A hA hsub
  simpa only [chart_selected] using h

theorem coordinateChart_image (q : Differential X) (i : Regular q) (B : Set Plane)
    (hB : MeasurableSet B) (hsub : B ⊆ (coordinateChart q i).target) :
    regularArea q ((coordinateChart q i).symm '' B) = volume B := by
  have h := primitive_chart_image q (selectedIndex q i) B hB hsub
  simpa only [chart_selected] using h

/-- The intrinsic primitive formulas characterize this measure uniquely. -/
theorem unique (q : Differential X) (ν : Measure (Regular q))
    (hν : ∀ (i : Index q) (A : Set (Regular q)), MeasurableSet A → A ⊆ (chart q i).source →
      ν A = volume (chart q i '' A)) : ν = regularArea q :=
  TranslationAtlasMeasure.unique (chart q) (selectedCover q) ν hν

/-- Any countable assembly from ANY covering family of genuine q-primitives
produces exactly the same measure, including different primitive choices. -/
theorem gluing_independent (q : Differential X) {J : Type*} (f : J → Index q)
    (C : TranslationAtlasMeasure.Cover (fun j => chart q (f j))) :
    TranslationAtlasMeasure.area (fun j => chart q (f j)) C = regularArea q := by
  apply unique q
  intro i A hA hsub
  exact TranslationAtlasMeasure.area_in_chart (fun j => chart q (f j)) C (chart q i)
    (fun j => NativePrimitiveAreaCharts.transition_locally_translation q (f j) i) A hA hsub

/-- Even a single pointwise selected primitive-chart cover determines the
same canonical area; no compatibility/MP assumption on a candidate is used. -/
theorem unique_from_coordinateCharts (q : Differential X) (ν : Measure (Regular q))
    (hν : ∀ (i : Regular q) (A : Set (Regular q)), MeasurableSet A → A ⊆ (coordinateChart q i).source →
      ν A = volume (coordinateChart q i '' A)) : ν = regularArea q := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  let : Nonempty (Regular q) := regular_nonempty q
  obtain ⟨C⟩ := TranslationAtlasMeasure.exists_cover (coordinateChart q)
    (fun x : Regular q => ⟨x, coordinateChart_center q x⟩)
  have hνeq := TranslationAtlasMeasure.unique (coordinateChart q) C ν hν
  have hμeq := TranslationAtlasMeasure.unique (coordinateChart q) C (regularArea q)
    (fun i A hA hsub => coordinateChart_formula q i A hA hsub)
  exact hνeq.trans hμeq.symm

theorem regularArea_isOpenPosMeasure (q : Differential X) : Measure.IsOpenPosMeasure (regularArea q) :=
  TranslationAtlasMeasure.area_isOpenPosMeasure (chart q) (selectedCover q)
    (NativePrimitiveAreaCharts.transition_locally_translation q)

theorem positive_open_mass (q : Differential X) (U : Set (Regular q)) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < regularArea q U := by
  let : Measure.IsOpenPosMeasure (regularArea q) := regularArea_isOpenPosMeasure q
  exact pos_iff_ne_zero.mpr (hU.measure_ne_zero (regularArea q) hne)

theorem support_eq_univ (q : Differential X) : (regularArea q).support = univ :=
  TranslationAtlasMeasure.area_support_eq_univ (chart q) (selectedCover q)
    (NativePrimitiveAreaCharts.transition_locally_translation q)

end MNEC.NativeRegularArea
