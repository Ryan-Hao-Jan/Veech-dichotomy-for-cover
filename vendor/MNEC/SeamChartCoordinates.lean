module

public import MNEC.SeamCharts

/-!
# Physical seam coordinates and transitions at the seam axis

The formulas identify the actual two torus pieces and their common seam.
Charts of the same seam label agree on their physical source overlaps.
At an axis point, equality in the constructed surface forces both labels
and physical inputs to agree, giving an identity transition near that point.
-/

noncomputable section
@[expose] public section

namespace MNEC.SeamChartCoordinates

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts SlitConnectedSum
open SeamChartMaps SeamChartAxis SeamChartOffAxis SeamCharts Set Topology
open scoped Classical

def coordinates {L₁ : Lattice} {w : Plane} (hw₁ : L₁.EmbeddedSlit w)
    (k : Bool) (p : Plane) : Plane :=
  (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm p

theorem coordinates_mem {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) :
    coordinates hw₁ k p ∈ rectangle C.a C.b C.r := by
  rw [physicalChart_source] at hp
  exact hp

theorem coordinates_longitudinal {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) :
    0 < (coordinates hw₁ k p).1 ∧ (coordinates hw₁ k p).1 < 1 := by
  have h := coordinates_mem hw₁ hw₂ C k p hp
  exact ⟨C.a_pos.trans h.1.1, h.1.2.trans C.b_lt_one⟩

theorem physicalChart_apply {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) :
    physicalChart hw₁ hw₂ C k p =
      chart C k ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ := by
  change coordinateChart hw₁ hw₂ C k (coordinates hw₁ k p) = _
  exact coordinateChart_apply hw₁ hw₂ C k _ _

theorem physicalChart_positive {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hpos : 0 < (coordinates hw₁ k p).2) :
    physicalChart hw₁ hw₂ C k p = left L₁ L₂ w (upper L₁ w (L₁.project p)) := by
  rw [physicalChart_apply hw₁ hw₂ C k p hp]
  have h := chart_positive_off C (embeddedSlit_ne_zero L₁ w hw₁) k
    ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ hpos
  simpa only [coordinates, Homeomorph.apply_symm_apply, leftOff] using h

theorem physicalChart_negative {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hneg : (coordinates hw₁ k p).2 < 0) :
    physicalChart hw₁ hw₂ C k p = right L₁ L₂ w (upper L₂ w (L₂.project p)) := by
  rw [physicalChart_apply hw₁ hw₂ C k p hp]
  have h := chart_negative_off C (embeddedSlit_ne_zero L₁ w hw₁) k
    ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ hneg
  simpa only [coordinates, Homeomorph.apply_symm_apply, rightOff] using h

theorem physicalChart_axis {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hzero : (coordinates hw₁ k p).2 = 0) :
    physicalChart hw₁ hw₂ C k p = left L₁ L₂ w
      (interiorBank L₁ w k (coordinates hw₁ k p).1
        (coordinates_longitudinal hw₁ hw₂ C k p hp)) := by
  rw [physicalChart_apply hw₁ hw₂ C k p hp]
  let q : Domain C := ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩
  change chart C k q = _
  rw [chart_zero C k q hzero]
  unfold positiveExtension
  rw [halfLift_zero C.leftCollar k (leftAbsHalf C q)
    (by change |(coordinates hw₁ k p).2| = 0; rw [hzero, abs_zero])]
  rfl

theorem physical_axis_position {L₁ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (k : Bool) (p : Plane)
    (hzero : (coordinates hw₁ k p).2 = 0) :
    p = (coordinates hw₁ k p).1 • w := by
  calc
    p = signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k (coordinates hw₁ k p) :=
      (Homeomorph.apply_symm_apply _ p).symm
    _ = (coordinates hw₁ k p).1 • w +
        (sideSign k * (coordinates hw₁ k p).2) • normal w := signedFrame_apply _ _ _ _
    _ = (coordinates hw₁ k p).1 • w := by rw [hzero, mul_zero, zero_smul, add_zero]

theorem offTrace_physicalChart_eq_none_iff {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) :
    offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = none ↔
      (coordinates hw₁ k p).2 = 0 := by
  constructor
  · intro htrace
    by_contra hne
    rw [physicalChart_apply hw₁ hw₂ C k p hp] at htrace
    let q : Domain C := ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩
    change offTrace L₁ L₂ w (chart C k q) = none at htrace
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [chart_negative_off C (embeddedSlit_ne_zero L₁ w hw₁) k q hneg,
        offTrace_rightOff] at htrace
      cases htrace
    · rw [chart_positive_off C (embeddedSlit_ne_zero L₁ w hw₁) k q hpos,
        offTrace_leftOff] at htrace
      cases htrace
  · intro hzero
    rw [physicalChart_axis hw₁ hw₂ C k p hp hzero]
    have hslit : L₁.project ((coordinates hw₁ k p).1 • w) ∈ L₁.slitSet w :=
      ⟨⟨(coordinates hw₁ k p).1,
        (coordinates_longitudinal hw₁ hw₂ C k p hp).1.le,
        (coordinates_longitudinal hw₁ hw₂ C k p hp).2.le⟩, rfl⟩
    change (if L₁.project ((coordinates hw₁ k p).1 • w) ∈ L₁.slitSet w then none
      else some (Sum.inl (L₁.project ((coordinates hw₁ k p).1 • w)))) = none
    exact ite_eq_left hslit

theorem physicalCharts_agree_on_overlap {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C D : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hpC : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hpD : p ∈ (physicalChart hw₁ hw₂ D k).source) :
    physicalChart hw₁ hw₂ C k p = physicalChart hw₁ hw₂ D k p := by
  rw [physicalChart_apply hw₁ hw₂ C k p hpC, physicalChart_apply hw₁ hw₂ D k p hpD]
  exact chart_eq_of_same_coordinates C D k _ _ rfl

theorem physicalChart_eq_at_axis {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C D : CommonCollar L₁ L₂ w) (k l : Bool) (p q : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hq : q ∈ (physicalChart hw₁ hw₂ D l).source)
    (hzero : (coordinates hw₁ k p).2 = 0)
    (heq : physicalChart hw₁ hw₂ C k p = physicalChart hw₁ hw₂ D l q) :
    k = l ∧ p = q := by
  have hzeroD : (coordinates hw₁ l q).2 = 0 := by
    apply (offTrace_physicalChart_eq_none_iff hw₁ hw₂ D l q hq).1
    rw [← heq]
    exact (offTrace_physicalChart_eq_none_iff hw₁ hw₂ C k p hp).2 hzero
  rw [physicalChart_axis hw₁ hw₂ C k p hp hzero,
    physicalChart_axis hw₁ hw₂ D l q hq hzeroD] at heq
  have hdata := (SeamClasses.left_interiorBank_eq_iff L₁ L₂ w hw₁ hw₂ k l
    (coordinates hw₁ k p).1 (coordinates hw₁ l q).1
    (coordinates_longitudinal hw₁ hw₂ C k p hp)
    (coordinates_longitudinal hw₁ hw₂ D l q hq)).1 heq
  refine ⟨hdata.2, ?_⟩
  rw [physical_axis_position hw₁ k p hzero, physical_axis_position hw₁ l q hzeroD, hdata.1]

theorem physical_transition_identity_on_overlap {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C D : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source ∩ (physicalChart hw₁ hw₂ D k).source) :
    (physicalChart hw₁ hw₂ D k).symm (physicalChart hw₁ hw₂ C k p) = p := by
  rw [physicalCharts_agree_on_overlap hw₁ hw₂ C D k p hp.1 hp.2]
  exact (physicalChart hw₁ hw₂ D k).left_inv hp.2

/-- A transition at an actual seam point is identity on an explicitly open neighborhood. -/
theorem physical_transition_identity_near_axis {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C D : CommonCollar L₁ L₂ w) (k l : Bool) (p q : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hq : q ∈ (physicalChart hw₁ hw₂ D l).source)
    (hzero : (coordinates hw₁ k p).2 = 0)
    (heq : physicalChart hw₁ hw₂ C k p = physicalChart hw₁ hw₂ D l q) :
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧
      U ⊆ (physicalChart hw₁ hw₂ C k).source ∩ (physicalChart hw₁ hw₂ D l).source ∧
      ∀ z ∈ U, (physicalChart hw₁ hw₂ D l).symm (physicalChart hw₁ hw₂ C k z) = z := by
  obtain ⟨rfl, rfl⟩ := physicalChart_eq_at_axis hw₁ hw₂ C D k l p q hp hq hzero heq
  refine ⟨(physicalChart hw₁ hw₂ C k).source ∩ (physicalChart hw₁ hw₂ D k).source,
    (physicalChart hw₁ hw₂ C k).open_source.inter (physicalChart hw₁ hw₂ D k).open_source,
    ⟨hp, hq⟩, Set.Subset.rfl, ?_⟩
  intro z hz
  exact physical_transition_identity_on_overlap hw₁ hw₂ C D k z hz

end MNEC.SeamChartCoordinates
