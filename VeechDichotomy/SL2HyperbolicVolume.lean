module

public import VeechDichotomy.SL2HyperbolicCoordinates
public import VeechDichotomy.HyperbolicAreaSupport
public import Mathlib.MeasureTheory.Group.Prod

/-! Construct the actual SL2 Haar volume from hyperbolic area and the
normalized Haar probability on its compact stabilizer at i. The genuine
coordinate cocycle proves left invariance; homeomorphic coordinates
prove finiteness on compact sets and positivity on nonempty open sets. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2HyperbolicVolume

open LinearGroup SL2HyperbolicCoordinates MeasureTheory Topology
open scoped UpperHalfPlane

def angularMeasure : Measure isotropy := Measure.haarMeasure ⊤

instance angularMeasure_haar : Measure.IsHaarMeasure angularMeasure := by
  dsimp only [angularMeasure]
  infer_instance

instance angularMeasure_probability : IsProbabilityMeasure angularMeasure :=
  IsProbabilityMeasure.mk Measure.haarMeasure_self

def cocycle (g : SL2) (z : ℍ) : isotropy := coordinate (g * z.toSL2R)

theorem continuous_cocycle (g : SL2) : Continuous (cocycle g) :=
  continuous_coordinate.comp (continuous_const.mul UpperHalfPlane.continuous_toSL2R)

theorem cocycle_relation (g : SL2) (z : ℍ) :
    (g • z).toSL2R * (cocycle g z : SL2) = g * z.toSL2R := by
  have hproj : (g * z.toSL2R) • UpperHalfPlane.I = g • z := by
    rw [mul_smul, UpperHalfPlane.toSL2R_smul_I]
  change (g • z).toSL2R * (((g * z.toSL2R) • UpperHalfPlane.I).toSL2R⁻¹ * (g * z.toSL2R)) = _
  rw [hproj]
  simp

def skew (g : SL2) (p : ℍ × isotropy) : ℍ × isotropy := (g • p.1, cocycle g p.1 * p.2)

theorem measurable_skew (g : SL2) : Measurable (skew g) :=
  ((continuous_const_smul g).comp continuous_fst).measurable.prodMk
    (((continuous_cocycle g).comp continuous_fst).mul continuous_snd).measurable

theorem measurePreserving_skew (g : SL2) :
    MeasurePreserving (skew g) ((volume : Measure ℍ).prod angularMeasure)
      ((volume : Measure ℍ).prod angularMeasure) := by
  change MeasurePreserving (fun p : ℍ × isotropy => (g • p.1, cocycle g p.1 * p.2)) _ _
  apply (measurePreserving_smul g (volume : Measure ℍ)).skew_product (g := fun z k => cocycle g z * k)
    (((continuous_cocycle g).comp continuous_fst).mul continuous_snd).measurable
  exact Filter.Eventually.of_forall (fun z => map_mul_left_eq_self angularMeasure (cocycle g z))

def hyperbolicVolume : Measure SL2 := ((volume : Measure ℍ).prod angularMeasure).map measurableEquiv

instance hyperbolicVolume_leftInvariant : hyperbolicVolume.IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    change (((volume : Measure ℍ).prod angularMeasure).map measurableEquiv).map (fun x => g * x) = _
    rw [Measure.map_map (measurable_const_mul g) measurableEquiv.measurable]
    have heq : (fun x => g * x) ∘ measurableEquiv = measurableEquiv ∘ skew g := by
      funext p
      change g * (p.1.toSL2R * (p.2 : SL2)) = (g • p.1).toSL2R * ((cocycle g p.1 : SL2) * (p.2 : SL2))
      rw [← mul_assoc ((g • p.1).toSL2R) (cocycle g p.1 : SL2) (p.2 : SL2), cocycle_relation, mul_assoc]
    rw [heq, ← Measure.map_map measurableEquiv.measurable (measurable_skew g),
      (measurePreserving_skew g).map_eq]
    rfl

instance hyperbolicVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts hyperbolicVolume where
  lt_top_of_isCompact K hK := by
    rw [hyperbolicVolume, Measure.map_apply measurableEquiv.measurable hK.measurableSet]
    exact (homeomorph.isCompact_preimage.mpr hK).measure_lt_top

instance hyperbolicVolume_openPos : hyperbolicVolume.IsOpenPosMeasure :=
  homeomorph.continuous.isOpenPosMeasure_map homeomorph.surjective

instance hyperbolicVolume_haar : Measure.IsHaarMeasure hyperbolicVolume := {}

theorem projection_volume {S : Set ℍ} (hS : MeasurableSet S) :
    hyperbolicVolume ((fun g : SL2 => g • UpperHalfPlane.I) ⁻¹' S) = volume S := by
  have hm : Measurable (fun g : SL2 => g • UpperHalfPlane.I) :=
    (continuous_id.smul continuous_const).measurable
  rw [hyperbolicVolume, Measure.map_apply measurableEquiv.measurable (hm hS)]
  have heq : measurableEquiv ⁻¹' ((fun g : SL2 => g • UpperHalfPlane.I) ⁻¹' S) = S ×ˢ Set.univ := by
    ext p
    change (p.1.toSL2R * (p.2 : SL2)) • UpperHalfPlane.I ∈ S ↔ p.1 ∈ S ∧ p.2 ∈ Set.univ
    rw [project_product]
    simp
  rw [heq, Measure.prod_prod, measure_univ, mul_one]

end VeechDichotomy.SL2HyperbolicVolume
