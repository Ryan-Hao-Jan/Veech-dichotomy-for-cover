module

public import MNEC.FlatChartDerivatives

/-!
# Intrinsic smooth directional fields on the actual regular locus

The field is the native pullback of a constant physical vector through
the chosen actual regular chart. Proved identity chart derivatives make
this independent of the chosen chart. Smoothness is proved as a map into
the actual native tangent bundle using its proved coordinate changes.
-/

noncomputable section
@[expose] public section

namespace MNEC.FlatVectorField

open LatticeTorus RegularChartedSpace FlatChartDerivatives Set Topology Filter
open scoped Manifold ContDiff Bundle

section ActualManifold

variable {L₁ L₂ : Lattice} {w : Plane}
variable (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)

def field (v : Plane) :
    letI := chartedSpace hw₁ hw₂
    ∀ x : Regular L₁ L₂ w, TangentSpace 𝓘(ℝ, Plane) x := by
  let := chartedSpace hw₁ hw₂
  exact fun x => VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
    (regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ x)) (fun _ : Plane => v) x

/-- This equality uses the native model-space synonym for the tangent space;
the actual intrinsic coordinate statement is `coordinate_formula`. -/
theorem field_eq_const (v : Plane) (x : Regular L₁ L₂ w) :
    letI := chartedSpace hw₁ hw₂
    field hw₁ hw₂ v x = v := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  unfold field VectorField.mpullback
  rw [mfderiv_regularChart_id hw₁ hw₂ (chosenIndex hw₁ hw₂ x) x
    (chosen_chart_source hw₁ hw₂ x)]
  have h : (ContinuousLinearMap.id ℝ Plane).inverse v = v := by
    rw [ContinuousLinearMap.inverse_id]
    rfl
  simpa only [] using! h

theorem field_eq_pullback_in_chart (v : Plane) (i : RegularAtlasCoverage.Index L₁ L₂ w)
    (x : Regular L₁ L₂ w) (hx : x ∈ (regularChart hw₁ hw₂ i).source) :
    letI := chartedSpace hw₁ hw₂
    field hw₁ hw₂ v x =
      VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularChart hw₁ hw₂ i)
        (fun _ : Plane => v) x := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  rw [field_eq_const]
  unfold VectorField.mpullback
  rw [mfderiv_regularChart_id hw₁ hw₂ i x hx]
  have h : v = (ContinuousLinearMap.id ℝ Plane).inverse v := by
    rw [ContinuousLinearMap.inverse_id]
    rfl
  simpa only [] using! h

/-- Every actual regular physical chart sends the intrinsic field to the specified physical vector. -/
theorem coordinate_formula (v : Plane) (i : RegularAtlasCoverage.Index L₁ L₂ w)
    (x : Regular L₁ L₂ w) (hx : x ∈ (regularChart hw₁ hw₂ i).source) :
    letI := chartedSpace hw₁ hw₂
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularChart hw₁ hw₂ i) x (field hw₁ hw₂ v x) = v := by
  let := chartedSpace hw₁ hw₂
  rw [mfderiv_regularChart_id hw₁ hw₂ i x hx, field_eq_const]
  rfl

theorem trivialization_formula (v : Plane) (x y : Regular L₁ L₂ w)
    (hy : y ∈ (regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ x)).source) :
    letI := chartedSpace hw₁ hw₂
    letI : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
    (trivializationAt Plane (TangentSpace 𝓘(ℝ, Plane)) x
      (⟨y, field hw₁ hw₂ v y⟩ : TangentBundle 𝓘(ℝ, Plane) (Regular L₁ L₂ w))).2 = v := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  rw [TangentBundle.trivializationAt_apply]
  change tangentCoordChange 𝓘(ℝ, Plane) y x y (field hw₁ hw₂ v y) = v
  rw [tangentCoordChange_to_chart_id hw₁ hw₂ x y hy, field_eq_const]
  rfl

/-- Smoothness is proved for the actual section into the native tangent bundle. -/
theorem contMDiff_field (v : Plane) :
    letI := chartedSpace hw₁ hw₂
    letI : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
    ContMDiff 𝓘(ℝ, Plane) (𝓘(ℝ, Plane)).tangent ∞
      (fun x : Regular L₁ L₂ w =>
        (⟨x, field hw₁ hw₂ v x⟩ : TangentBundle 𝓘(ℝ, Plane) (Regular L₁ L₂ w))) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  intro x
  rw [Bundle.contMDiffAt_section]
  apply contMDiffAt_const.congr_of_eventuallyEq
  filter_upwards [(chartAt Plane x).open_source.mem_nhds (mem_chart_source Plane x)] with y hy
  exact trivialization_formula hw₁ hw₂ v x y hy

end ActualManifold

end MNEC.FlatVectorField
