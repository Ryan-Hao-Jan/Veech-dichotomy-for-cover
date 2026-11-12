module

public import MNEC.NativeFiniteRegularArea
public import MNEC.NativePhysicalArea
public import MNEC.NativeCompleteDirectionalArea
public import Mathlib.Tactic.GCongr

/-! Actual finite positive flat area and its probability normalization on
the ORIGINAL native curve and regular locus. All total-mass hypotheses are
discharged by the original-chart coefficient/Jacobian compact-cover proof.
The complete native phase has finite raw area and normalized mass <=1;
probability on that phase still requires the separate AE-completeness proof. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeProbabilityArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeFiniteRegularArea
open MeasureTheory Set
open scoped ENNReal Classical Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem surfaceArea_isFinite (q : Differential X) : IsFiniteMeasure (NativePhysicalArea.surfaceArea q) where
  measure_univ_lt_top := by
    rw [NativePhysicalArea.surfaceArea_univ]
    exact (regularArea_isFinite q).measure_univ_lt_top

theorem surfaceArea_univ_pos (q : Differential X) : 0 < NativePhysicalArea.surfaceArea q univ := by
  rw [NativePhysicalArea.surfaceArea_univ]
  exact regularArea_univ_pos q

theorem surfaceArea_univ_eq_ofReal_totalArea (q : Differential X) :
    NativePhysicalArea.surfaceArea q univ = ENNReal.ofReal (totalArea q) := by
  rw [NativePhysicalArea.surfaceArea_univ, ofReal_totalArea]

def normalizedRegularArea (q : Differential X) : Measure (Regular q) :=
  (NativeRegularArea.regularArea q univ)⁻¹ • NativeRegularArea.regularArea q

def normalizedArea (q : Differential X) : Measure X :=
  (NativeRegularArea.regularArea q univ)⁻¹ • NativePhysicalArea.surfaceArea q

theorem normalizedRegularArea_probability (q : Differential X) : IsProbabilityMeasure (normalizedRegularArea q) where
  measure_univ := by
    rw [normalizedRegularArea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (regularArea_univ_pos q).ne' (regularArea_univ_ne_top q)

theorem normalizedArea_probability (q : Differential X) : IsProbabilityMeasure (normalizedArea q) where
  measure_univ := by
    rw [normalizedArea, Measure.smul_apply, smul_eq_mul, NativePhysicalArea.surfaceArea_univ]
    exact ENNReal.inv_mul_cancel (regularArea_univ_pos q).ne' (regularArea_univ_ne_top q)

theorem normalized_inclusion_measurePreserving (q : Differential X) :
    MeasurePreserving (Subtype.val : Regular q → X) (normalizedRegularArea q) (normalizedArea q) :=
  (NativePhysicalArea.regular_inclusion_measurePreserving q).smul_measure _

theorem normalizedArea_zeroSet (q : Differential X) : normalizedArea q (zeroSet q) = 0 := by
  rw [normalizedArea, Measure.smul_apply, NativePhysicalArea.surfaceArea_zeroSet, smul_zero]

theorem normalized_partial_timeMap_measurePreserving (q : Differential X) (v : Plane) (t : ℝ) :
    MeasurePreserving (NativePartialDirectionalFlow.timeMap q v t)
      ((normalizedRegularArea q).restrict (NativePartialDirectionalFlow.timeMap q v t).source)
      ((normalizedRegularArea q).restrict (NativePartialDirectionalFlow.timeMap q v t).target) := by
  simpa only [normalizedRegularArea, Measure.restrict_smul] using
    (NativePartialDirectionalArea.timeMap_measurePreserving q v t).smul_measure
      (NativeRegularArea.regularArea q univ)⁻¹

theorem completeArea_isFinite (q : Differential X) (v : Plane) :
    IsFiniteMeasure (NativeCompleteDirectionalArea.completeArea q v) where
  measure_univ_lt_top := (NativeCompleteDirectionalArea.completeArea_univ_le q v).trans_lt
    (regularArea_isFinite q).measure_univ_lt_top

theorem normalizedCompleteArea_univ_le_one (q : Differential X) (v : Plane) :
    NativeCompleteDirectionalArea.normalizedCompleteArea q v univ ≤ 1 := by
  rw [NativeCompleteDirectionalArea.normalizedCompleteArea, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (NativeRegularArea.regularArea q univ)⁻¹ * NativeRegularArea.regularArea q univ :=
      by gcongr; exact NativeCompleteDirectionalArea.completeArea_univ_le q v
    _ = 1 := ENNReal.inv_mul_cancel (regularArea_univ_pos q).ne' (regularArea_univ_ne_top q)

end MNEC.NativeProbabilityArea

