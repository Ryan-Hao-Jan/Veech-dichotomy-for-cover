module

public import MNEC.NativePartialDirectionalFlow
public import MNEC.NativeRegularArea
public import MNEC.LocalAreaGluing

/-! Canonical physical area is preserved by the ACTUAL native maximal
partial flow of an arbitrary original holomorphic differential. Actual
primitive-chart Lebesgue formulas prove physical-ball and finite-word
area identities; native word coverage and second countability glue them
over the full actual domain. No area compatibility, preservation,
completeness or finite-total-mass certificate is assumed. -/

@[expose] public section
noncomputable section
namespace MNEC.NativePartialDirectionalArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativePartialDirectionalFlow MeasureTheory Set Topology
open scoped ENNReal Classical Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

abbrev Ball (q : Differential X) := letI := chartedSpace q; TranslationBallCharts.BallChart (Regular q)

def ballModel (q : Differential X) (B : Ball q) : OpenPartialHomeomorph Plane (Regular q) := by
  let := chartedSpace q
  exact TranslationBallCharts.model B

def ballTimeMap (q : Differential X) (B : Ball q) (v : Plane) (t : ℝ) :
    OpenPartialHomeomorph (Regular q) (Regular q) := by
  let := chartedSpace q
  exact TranslationBallCharts.timeMap B v t

theorem ball_model_image_area (q : Differential X) (B : Ball q) (V : Set Plane)
    (hV : MeasurableSet V) (hsub : V ⊆ (ballModel q B).source) :
    NativeRegularArea.regularArea q (ballModel q B '' V) = volume V := by
  let := chartedSpace q
  have hmem : B.chart ∈ atlas Plane (Regular q) := B.mem_atlas
  change B.chart ∈ range (coordinateChart q) at hmem
  obtain ⟨i, hi⟩ := hmem
  have hsubTarget : V ⊆ (coordinateChart q i).target := by
    intro p hp
    rw [hi]
    exact B.ball_subset ((TranslationBallCharts.model_source B) ▸ hsub hp)
  change NativeRegularArea.regularArea q (B.chart.symm '' V) = volume V
  rw [← hi]
  exact NativeRegularArea.coordinateChart_image q i V hV hsubTarget

theorem ball_timeMap_image_area (q : Differential X) (B : Ball q) (v : Plane) (t : ℝ)
    (V : Set (Regular q)) (hV : MeasurableSet V) (hsub : V ⊆ (ballTimeMap q B v t).source) :
    NativeRegularArea.regularArea q (ballTimeMap q B v t '' V) = NativeRegularArea.regularArea q V := by
  let := chartedSpace q
  exact RegularCoordinateArea.translationTimeMap_image_area (NativeRegularArea.regularArea q)
    (TranslationBallCharts.model B) (ball_model_image_area q B) v t V hV hsub

theorem word_image_area (q : Differential X) (v : Plane) (W : List (Step q))
    (A : Set (Regular q)) (hA : MeasurableSet A) (hsource : A ⊆ (wordMap q v W).source) :
    NativeRegularArea.regularArea q (wordMap q v W '' A) = NativeRegularArea.regularArea q A := by
  let := chartedSpace q
  exact DirectionalFlowWords.compose_image_area (NativeRegularArea.regularArea q)
    (TranslationFlowWords.stepMap v) (fun S => ball_timeMap_image_area q S.1 v S.2) W A hA hsource

theorem timeMap_image_area (q : Differential X) (v : Plane) (t : ℝ)
    (A : Set (Regular q)) (hA : MeasurableSet A) (hsource : A ⊆ (timeMap q v t).source) :
    NativeRegularArea.regularArea q (timeMap q v t '' A) = NativeRegularArea.regularArea q A := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  let ι := {W : List (Step q) // elapsed q W = t}
  let E : ι → OpenPartialHomeomorph (Regular q) (Regular q) := fun W => wordMap q v W.val
  let U : ι → Set (Regular q) := fun W => (E W).source
  have hcover : (timeMap q v t).source ⊆ ⋃ W : ι, U W := by
    intro x hx
    obtain ⟨W, htime, hW⟩ := word_of_mem_domain q v x t hx
    exact mem_iUnion.mpr ⟨⟨W, htime⟩, hW⟩
  have hagrees : ∀ W : ι, EqOn (timeMap q v t) (E W) (U W) := by
    intro W x hx
    have h := (word_native_identification q v W.val x hx).2
    rw [W.property] at h
    exact h.symm
  exact LocalAreaGluing.image_area_of_open_cover (NativeRegularArea.regularArea q) (timeMap q v t)
    U E (fun W => (E W).open_source) hcover (fun _ => subset_refl _) hagrees
      (fun W => word_image_area q v W.val) A hA hsource

theorem timeMap_image_measurable (q : Differential X) (v : Plane) (t : ℝ)
    (A : Set (Regular q)) (hA : MeasurableSet A) (hsource : A ⊆ (timeMap q v t).source) :
    MeasurableSet (timeMap q v t '' A) :=
  LocalAreaGluing.measurableSet_image_of_subset_source _ A hA hsource

theorem trajectory_outside (q : Differential X) (v : Plane) (t : ℝ) (x : Regular q)
    (hx : t ∉ NativeDirectionalDynamics.domain q v x) : NativeDirectionalDynamics.trajectory q v x t = x := by
  let := chartedSpace q
  change MaximalIntegralCurve.maximalCurve (TranslationAtlasField.field v) x t = x
  change t ∉ MaximalIntegralCurve.maximalDomain (TranslationAtlasField.field v) x at hx
  rw [MaximalIntegralCurve.maximalCurve, dite_eq_right hx]

theorem measurable_timeMap (q : Differential X) (v : Plane) (t : ℝ) : Measurable (timeMap q v t) := by
  let F := timeMap q v t
  have houtside : ∀ x ∉ F.source, F x = x := fun x hx => trajectory_outside q v t x hx
  have hmeas : Measurable (F.source.piecewise (F : Regular q → Regular q) id) :=
    F.continuousOn.measurable_piecewise continuous_id.continuousOn F.open_source.measurableSet
  have heq : F.source.piecewise (F : Regular q → Regular q) id = F := by
    funext x
    by_cases hx : x ∈ F.source
    · simp [hx]
    · simpa [hx] using (houtside x hx).symm
  rwa [heq] at hmeas

theorem timeMap_preimage_area (q : Differential X) (v : Plane) (t : ℝ)
    (N : Set (Regular q)) (hN : MeasurableSet N) :
    NativeRegularArea.regularArea q ((timeMap q v t).source ∩ timeMap q v t ⁻¹' N) =
      NativeRegularArea.regularArea q ((timeMap q v t).target ∩ N) := by
  let F := timeMap q v t
  let A := F.source ∩ F ⁻¹' N
  have hA : MeasurableSet A := F.open_source.measurableSet.inter (hN.preimage (measurable_timeMap q v t))
  have harea := timeMap_image_area q v t A hA inter_subset_left
  have himage : F '' A = F.target ∩ N := by
    have heq : F.symm '' (F.target ∩ N) = A := by
      simpa only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target,
        OpenPartialHomeomorph.symm_symm] using F.symm.image_source_inter_eq' N
    rw [← heq]
    exact F.image_symm_image_of_subset_target inter_subset_left
  change NativeRegularArea.regularArea q (F '' A) = NativeRegularArea.regularArea q A at harea
  rw [himage] at harea
  exact harea.symm

theorem time_preimage_area_le (q : Differential X) (v : Plane) (t : ℝ)
    (N : Set (Regular q)) (hN : MeasurableSet N) :
    NativeRegularArea.regularArea q {x | t ∈ NativeDirectionalDynamics.domain q v x ∧
      NativeDirectionalDynamics.trajectory q v x t ∈ N} ≤ NativeRegularArea.regularArea q N := by
  change NativeRegularArea.regularArea q ((timeMap q v t).source ∩ timeMap q v t ⁻¹' N) ≤ _
  rw [timeMap_preimage_area q v t N hN]
  exact measure_mono inter_subset_right

theorem timeMap_restrict_map (q : Differential X) (v : Plane) (t : ℝ) :
    ((NativeRegularArea.regularArea q).restrict (timeMap q v t).source).map (timeMap q v t) =
      (NativeRegularArea.regularArea q).restrict (timeMap q v t).target := by
  apply Measure.ext
  intro N hN
  rw [Measure.map_apply (measurable_timeMap q v t) hN,
    Measure.restrict_apply' (timeMap q v t).open_source.measurableSet, Measure.restrict_apply hN]
  simpa only [inter_comm] using timeMap_preimage_area q v t N hN

theorem timeMap_measurePreserving (q : Differential X) (v : Plane) (t : ℝ) :
    MeasurePreserving (timeMap q v t)
      ((NativeRegularArea.regularArea q).restrict (timeMap q v t).source)
      ((NativeRegularArea.regularArea q).restrict (timeMap q v t).target) where
  measurable := measurable_timeMap q v t
  map_eq := timeMap_restrict_map q v t

end MNEC.NativePartialDirectionalArea

