module

public import VeechDichotomy.LinearEquivalences

/-! Actual SL2 deformation of the derived regular translation atlas on an
arbitrary compact translation surface. The underlying topology is unchanged;
the new charts are the old primitive charts followed by the given matrix.

This constructs the punctured surface only. Extension across the finite
zero set, and the resulting compact complex differential, remain separate
obligations and are not assumed here.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DeformedRegularAtlas

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open LinearGroup LinearEquivalences Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure DeformedRegular (q : Differential X) (A : SL2) where
  point : Regular q

instance topology (q : Differential X) (A : SL2) : TopologicalSpace (DeformedRegular q A) :=
  TopologicalSpace.induced DeformedRegular.point inferInstance

def toOriginal (q : Differential X) (A : SL2) : DeformedRegular q A ≃ₜ Regular q where
  toFun := DeformedRegular.point
  invFun := fun p => ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space (q : Differential X) (A : SL2) : T2Space (DeformedRegular q A) :=
  (toOriginal q A).isEmbedding.t2Space

instance secondCountable (q : Differential X) (A : SL2) :
    SecondCountableTopology (DeformedRegular q A) := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  exact (toOriginal q A).isEmbedding.secondCountableTopology

def chart (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    OpenPartialHomeomorph (DeformedRegular q A) Plane :=
  (toOriginal q A).transOpenPartialHomeomorph
    ((coordinateChart q i.point).transHomeomorph (planeEquiv A).toHomeomorph)

theorem chart_source (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    (chart q A i).source = DeformedRegular.point ⁻¹' (coordinateChart q i.point).source := rfl

theorem chart_target (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    (chart q A i).target = (planeEquiv A).symm ⁻¹' (coordinateChart q i.point).target := rfl

theorem chart_apply (q : Differential X) (A : SL2) (i p : DeformedRegular q A) :
    chart q A i p = planeEquiv A (coordinateChart q i.point p.point) := rfl

theorem chart_symm_point (q : Differential X) (A : SL2) (i : DeformedRegular q A) (p : Plane) :
    ((chart q A i).symm p).point = (coordinateChart q i.point).symm ((planeEquiv A).symm p) := rfl

theorem chart_center (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    i ∈ (chart q A i).source := coordinateChart_center q i.point

@[instance_reducible] def chartedSpace (q : Differential X) (A : SL2) :
    ChartedSpace Plane (DeformedRegular q A) where
  atlas := range (chart q A)
  chartAt := chart q A
  mem_chart_source := chart_center q A
  chart_mem_atlas i := ⟨i, rfl⟩

theorem transition_formula (q : Differential X) (A : SL2) (i j : DeformedRegular q A)
    (p : Plane) :
    ((chart q A i).symm.trans (chart q A j)) p =
      planeEquiv A (((coordinateChart q i.point).symm.trans (coordinateChart q j.point))
        ((planeEquiv A).symm p)) := rfl

theorem transition_locally_translation (q : Differential X) (A : SL2)
    (i j : DeformedRegular q A) :
    MNEC.TranslationGroupoid.LocallyTranslationOn ((chart q A i).symm.trans (chart q A j))
      ((chart q A i).symm.trans (chart q A j)).source := by
  intro p hp
  have hpold : (planeEquiv A).symm p ∈
      ((coordinateChart q i.point).symm.trans (coordinateChart q j.point)).source := hp
  obtain ⟨a, ha⟩ := MNEC.NativeRegularTranslationAtlas.transition_locally_translation q
    i.point j.point ((planeEquiv A).symm p) hpold
  refine ⟨planeEquiv A a, ?_⟩
  have hc : ContinuousAt (planeEquiv A).symm p := (planeEquiv A).symm.continuous.continuousAt
  filter_upwards [hc ha] with z hz
  rw [transition_formula, hz, map_add, ContinuousLinearEquiv.apply_symm_apply]

theorem has_translation_groupoid (q : Differential X) (A : SL2) :
    letI := chartedSpace q A
    HasGroupoid (DeformedRegular q A) MNEC.TranslationGroupoid.groupoid := by
  let := chartedSpace q A
  apply hasGroupoid_of_pregroupoid MNEC.TranslationGroupoid.pregroupoid
  intro e f he hf
  change e ∈ range (chart q A) at he
  change f ∈ range (chart q A) at hf
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hf
  exact transition_locally_translation q A i j

theorem isManifold (q : Differential X) (A : SL2) (n : ℕ∞ω) :
    letI := chartedSpace q A
    IsManifold 𝓘(ℝ, Plane) n (DeformedRegular q A) := by
  let := chartedSpace q A
  let : HasGroupoid (DeformedRegular q A) MNEC.TranslationGroupoid.groupoid :=
    has_translation_groupoid q A
  let : HasGroupoid (DeformedRegular q A) (contDiffGroupoid n 𝓘(ℝ, Plane)) :=
    hasGroupoid_of_le (G₁ := MNEC.TranslationGroupoid.groupoid) (by infer_instance)
      (MNEC.NativeRegularTranslationAtlas.translationGroupoid_le_contDiffGroupoid n)
  exact IsManifold.mk' 𝓘(ℝ, Plane) n (DeformedRegular q A)

end VeechDichotomy.DeformedRegularAtlas
