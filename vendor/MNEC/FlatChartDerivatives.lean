module

public import MNEC.RegularSmoothStructure
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Native derivatives of the actual regular physical charts

The proved local translations imply identity Fréchet derivatives of every
actual regular transition. The native manifold derivatives of the charts
are therefore identity maps in the tangent model, rather than assumptions
about the atlas or the vector field.
-/

noncomputable section
@[expose] public section

namespace MNEC.FlatChartDerivatives

open LatticeTorus RegularChartedSpace RegularTranslationStructure Set Topology Filter
open scoped Manifold ContDiff

theorem regular_transition_hasFDerivAt {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i j : RegularAtlasCoverage.Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j)).source) :
    HasFDerivAt ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j))
      (ContinuousLinearMap.id ℝ Plane) p := by
  obtain ⟨v, hv⟩ := regular_transition_property hw₁ hw₂ i j p hp
  have hbase : HasFDerivAt (fun y : Plane => y + v) (ContinuousLinearMap.id ℝ Plane) p :=
    (hasFDerivAt_id p).add_const v
  exact hbase.congr_of_eventuallyEq hv

theorem regular_transition_fderiv {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i j : RegularAtlasCoverage.Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j)).source) :
    fderiv ℝ ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j)) p =
      ContinuousLinearMap.id ℝ Plane :=
  (regular_transition_hasFDerivAt hw₁ hw₂ i j p hp).fderiv

section ActualManifold

variable {L₁ L₂ : Lattice} {w : Plane}
variable (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)

theorem chartAt_eq_regularChart (x : Regular L₁ L₂ w) :
    letI := chartedSpace hw₁ hw₂
    chartAt Plane x = regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ x) := rfl

theorem chosen_chart_source (x : Regular L₁ L₂ w) :
    x ∈ (regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ x)).source := by
  rw [regularChart_source]
  exact chosenIndex_mem_target hw₁ hw₂ x

theorem mfderiv_regularChart_id (i : RegularAtlasCoverage.Index L₁ L₂ w)
    (x : Regular L₁ L₂ w) (hx : x ∈ (regularChart hw₁ hw₂ i).source) :
    letI := chartedSpace hw₁ hw₂
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularChart hw₁ hw₂ i) x =
      ContinuousLinearMap.id ℝ Plane := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let j := chosenIndex hw₁ hw₂ x
  let e := regularChart hw₁ hw₂ j
  have hxE : x ∈ e.source := chosen_chart_source hw₁ hw₂ x
  have hp : e x ∈ (e.symm.trans (regularChart hw₁ hw₂ i)).source := by
    refine ⟨e.map_source hxE, ?_⟩
    change e.symm (e x) ∈ (regularChart hw₁ hw₂ i).source
    rw [e.left_inv hxE]
    exact hx
  have htransition := regular_transition_fderiv hw₁ hw₂ j i (e x) hp
  have hmem : regularChart hw₁ hw₂ i ∈ atlas Plane (Regular L₁ L₂ w) := ⟨i, rfl⟩
  have hdiff := mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) hmem hx
  rw [hdiff.mfderiv_abuse]
  simpa only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ,
    chartAt_eq_regularChart hw₁ hw₂, e, j] using! htransition

theorem tangentCoordChange_to_chart_id (x y : Regular L₁ L₂ w)
    (hy : y ∈ (regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ x)).source) :
    letI := chartedSpace hw₁ hw₂
    letI : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
    tangentCoordChange 𝓘(ℝ, Plane) y x y = ContinuousLinearMap.id ℝ Plane := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  have hy' : y ∈ (chartAt Plane x).source := hy
  rw [← mfderiv_chartAt_eq_tangentCoordChange hy', chartAt_eq_regularChart hw₁ hw₂]
  exact mfderiv_regularChart_id hw₁ hw₂ (chosenIndex hw₁ hw₂ x) y hy

theorem mdifferentiableAt_regularChart_symm (i : RegularAtlasCoverage.Index L₁ L₂ w)
    (y : Plane) (hy : y ∈ (regularChart hw₁ hw₂ i).target) :
    letI := chartedSpace hw₁ hw₂
    MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularChart hw₁ hw₂ i).symm y := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  have hmem : regularChart hw₁ hw₂ i ∈ atlas Plane (Regular L₁ L₂ w) := ⟨i, rfl⟩
  exact mdifferentiableAt_atlas_symm hmem hy

theorem mfderiv_regularChart_symm_id (i : RegularAtlasCoverage.Index L₁ L₂ w)
    (y : Plane) (hy : y ∈ (regularChart hw₁ hw₂ i).target) :
    letI := chartedSpace hw₁ hw₂
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularChart hw₁ hw₂ i).symm y =
      ContinuousLinearMap.id ℝ Plane := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let e := regularChart hw₁ hw₂ i
  have hmem : e ∈ atlas Plane (Regular L₁ L₂ w) := ⟨i, rfl⟩
  have he : e.MDifferentiable 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) := mdifferentiable_of_mem_atlas hmem
  have hcomp := he.comp_symm_deriv hy
  rw [mfderiv_regularChart_id hw₁ hw₂ i (e.symm y) (e.map_target hy)] at hcomp
  simpa only [ContinuousLinearMap.id_comp] using! hcomp

end ActualManifold

end MNEC.FlatChartDerivatives
