module

public import MNEC.RegularChartedSpace
public import MNEC.RegularAtlasTransitions
public import MNEC.TranslationGroupoid
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# A proved native translation structure on the actual regular quotient

The charted space is constructed from the proved physical chart cover.
Its compatibility with the native translation groupoid follows from the
actual transition theorem and mathlib's subtype-restriction identities.
No atlas compatibility is supplied as a field of the surface definition.
-/

noncomputable section
@[expose] public section

namespace MNEC.RegularTranslationStructure

open LatticeTorus SlitConnectedSum RegularAtlasCoverage RegularChartedSpace
open Set Topology TranslationGroupoid

theorem regular_transition_property {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i j : Index L₁ L₂ w) :
    LocallyTranslationOn
      ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j))
      ((regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j)).source := by
  let e := (RegularAtlasCoverage.chart hw₁ hw₂ i).symm
  let d := (RegularAtlasCoverage.chart hw₁ hw₂ j).symm
  let P := (RegularAtlasCoverage.chart hw₁ hw₂ i).trans
    (RegularAtlasCoverage.chart hw₁ hw₂ j).symm
  let U := e.target ∩ e.symm ⁻¹' (regularOpen hw₁ hw₂ : Set (Surface L₁ L₂ w))
  let R := P.restr U
  let E := (regularChart hw₁ hw₂ i).symm.trans (regularChart hw₁ hw₂ j)
  have hEq : E ≈ R := by
    have h := e.subtypeRestr_symm_trans_subtypeRestr
      (s := regularOpen hw₁ hw₂) (regular_nonempty L₁ L₂ w) d
    simpa only [E, R, P, U, regularChart, e, d, OpenPartialHomeomorph.symm_symm] using h
  have hR : pregroupoid.property R R.source := by
    intro p hp
    have hpP : p ∈ P.source := hp.1
    obtain ⟨v, hv⟩ := RegularAtlasTransitions.transition_locally_translation hw₁ hw₂ i j p hpP
    refine ⟨v, ?_⟩
    simpa only [R, OpenPartialHomeomorph.restr_apply] using hv
  exact mem_pregroupoid_of_eqOnSource pregroupoid (Setoid.symm hEq) hR

/-- The independently constructed regular charted space has the native local-translation groupoid. -/
theorem has_translation_groupoid {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    letI := chartedSpace hw₁ hw₂
    HasGroupoid (Regular L₁ L₂ w) TranslationGroupoid.groupoid := by
  let := chartedSpace hw₁ hw₂
  apply hasGroupoid_of_pregroupoid pregroupoid
  intro e e' he he'
  change e ∈ Set.range (regularChart hw₁ hw₂) at he
  change e' ∈ Set.range (regularChart hw₁ hw₂) at he'
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := he'
  exact regular_transition_property hw₁ hw₂ i j

end MNEC.RegularTranslationStructure
