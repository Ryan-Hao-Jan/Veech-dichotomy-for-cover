module

public import MNEC.SeamChartRange
public import MNEC.CollarRefinements

@[expose] public section

/-!
# Local openness of the seam rectangle map at the axis

A smaller actual common collar fits inside any open neighborhood of an
axis point. Its image is an open quotient neighborhood by the range and
saturation proofs, giving local openness at the seam itself.
-/

noncomputable section

namespace MNEC.SeamChartAxis

open LatticeTorus SlitConnectedSum SlitCollars SeamChartMaps SeamChartRange
open CollarRefinements Set Topology

theorem chart_eq_of_same_coordinates {L₁ L₂ : Lattice} {w : Plane}
    (C D : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (p : Domain D)
    (heq : q.val = p.val) : chart C k q = chart D k p := by
  rcases q with ⟨q, hq⟩
  rcases p with ⟨p, hp⟩
  change q = p at heq
  cases heq
  rfl

theorem exists_open_image_neighborhood_of_zero {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool)
    (V : Set (Domain C)) (hV : IsOpen V) (q : Domain C)
    (hqV : q ∈ V) (hq : q.val.2 = 0) :
    ∃ O : Set (Surface L₁ L₂ w), IsOpen O ∧ chart C k q ∈ O ∧ O ⊆ chart C k '' V := by
  let U : Set Plane := Subtype.val '' V
  have hrect : IsOpen (rectangle C.a C.b C.r) := isOpen_Ioo.prod isOpen_Ioo
  have hU : IsOpen U := hrect.isOpenMap_subtype_val V hV
  have hcenter : (q.val.1, 0) ∈ U := ⟨q, hqV, Prod.ext rfl hq⟩
  obtain ⟨D, htD, hD⟩ := exists_refinement_in_open C q.val.1 q.property.1 U hU hcenter
  let z : Domain D := ⟨(q.val.1, 0), ⟨htD, ⟨neg_lt_zero.mpr D.r_pos, D.r_pos⟩⟩⟩
  refine ⟨range (chart D k), range_chart_open hw₁ hw₂ D k, ?_, ?_⟩
  · exact ⟨z, chart_eq_of_same_coordinates D C k z q (Prod.ext rfl hq.symm)⟩
  · rintro p ⟨u, rfl⟩
    obtain ⟨v, hv, heq⟩ := (hD u.property).2
    exact ⟨v, hv, chart_eq_of_same_coordinates C D k v u heq⟩

end MNEC.SeamChartAxis
