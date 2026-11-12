module

public import MNEC.CutBankLifts

@[expose] public section

/-!
# Refinement of actual common physical slit collars

The geometric injection and slit-isolation properties survive restriction.
Every open neighborhood of an interior axis point contains a smaller common
collar. This concerns the physical coordinate rectangles and does not assume
that their maps into the seam quotient are open.
-/

noncomputable section

open scoped Topology

namespace MNEC.CollarRefinements

open LatticeTorus SlitCollars CutBankLifts Set Topology

theorem rectangle_mono {a b r a' b' r' : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hr : r' ≤ r) :
    rectangle a' b' r' ⊆ rectangle a b r := by
  intro p hp
  exact ⟨⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩,
    ⟨by linarith only [hp.2.1, hr], hp.2.2.trans_le hr⟩⟩

/-- Bank lifts depend only on the actual physical coordinates and the bank,
not on which verified collar contains those coordinates. -/
theorem halfLift_eq_of_same_coordinates {L : Lattice} {w : Plane}
    (C D : Collar L w) (k : Bool) (p : Plane)
    (hpC : p ∈ domain C) (hpD : p ∈ domain D) (hp : 0 ≤ p.2) :
    halfLift C k ⟨p, hpC, hp⟩ = halfLift D k ⟨p, hpD, hp⟩ := by
  rfl

end MNEC.CollarRefinements

namespace MNEC.SlitCollars.CommonCollar

open LatticeTorus OffSlitEmbeddings CollarRefinements Set

/-- Restrict a constructed common collar to a smaller physical rectangle. -/
def restrict {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (a' b' r' : ℝ) (ha : C.a ≤ a') (hab : a' < b') (hb : b' ≤ C.b)
    (hrpos : 0 < r') (hr : r' ≤ C.r) : CommonCollar L₁ L₂ w where
  a := a'
  b := b'
  r := r'
  a_pos := C.a_pos.trans_le ha
  a_lt_b := hab
  b_lt_one := hb.trans_lt C.b_lt_one
  r_pos := hrpos
  left_injective := C.left_injective.mono (rectangle_mono ha hb hr)
  right_injective := C.right_injective.mono (rectangle_mono ha hb hr)
  left_slit_iff := fun p hp => C.left_slit_iff p (rectangle_mono ha hb hr hp)
  right_slit_iff := fun p hp => C.right_slit_iff p (rectangle_mono ha hb hr hp)

theorem restrict_subset {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (a' b' r' : ℝ) (ha : C.a ≤ a') (hab : a' < b') (hb : b' ≤ C.b)
    (hrpos : 0 < r') (hr : r' ≤ C.r) :
    rectangle (C.restrict a' b' r' ha hab hb hrpos hr).a
      (C.restrict a' b' r' ha hab hb hrpos hr).b
      (C.restrict a' b' r' ha hab hb hrpos hr).r ⊆ rectangle C.a C.b C.r :=
  rectangle_mono ha hb hr

end MNEC.SlitCollars.CommonCollar

namespace MNEC.CollarRefinements

open LatticeTorus SlitCollars Set Topology

/-- A common physical subcollar can be fitted inside any given open
neighborhood of an interior point of its axis. -/
theorem exists_refinement_in_open {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (t : ℝ) (ht : t ∈ Ioo C.a C.b)
    (V : Set Plane) (hV : IsOpen V) (hcenter : (t, 0) ∈ V) :
    ∃ D : CommonCollar L₁ L₂ w, t ∈ Ioo D.a D.b ∧
      rectangle D.a D.b D.r ⊆ rectangle C.a C.b C.r ∩ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV (t, 0) hcenter
  let ρ := min (ε / 2)
    (min ((t - C.a) / 2) (min ((C.b - t) / 2) (C.r / 2)))
  have hρ : 0 < ρ :=
    lt_min (by positivity) (lt_min (by linarith only [ht.1])
      (lt_min (by linarith only [ht.2]) (by linarith only [C.r_pos])))
  have hρε : ρ ≤ ε / 2 := min_le_left _ _
  have hρa : ρ ≤ (t - C.a) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρb : ρ ≤ (C.b - t) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρr : ρ ≤ C.r / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρε' : ρ < ε := hρε.trans_lt (by linarith only [hε])
  have ha : C.a ≤ t - ρ := by linarith only [ht.1, hρa]
  have hab : t - ρ < t + ρ := by linarith only [hρ]
  have hb : t + ρ ≤ C.b := by linarith only [ht.2, hρb]
  have hr : ρ ≤ C.r := by linarith only [hρr, C.r_pos]
  let D := C.restrict (t - ρ) (t + ρ) ρ ha hab hb hρ hr
  refine ⟨D, ?_, ?_⟩
  · change t - ρ < t ∧ t < t + ρ
    constructor <;> linarith only [hρ]
  · intro p hp
    change p ∈ rectangle (t - ρ) (t + ρ) ρ at hp
    refine ⟨rectangle_mono ha hb hr hp, hball ?_⟩
    rw [← ball_prod_same]
    constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr
        ⟨by linarith only [hp.1.1, hρε'], by linarith only [hp.1.2, hρε']⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact abs_lt.mpr
        ⟨by linarith only [hp.2.1, hρε'], by linarith only [hp.2.2, hρε']⟩

/-- The neighborhood version also applies when the chosen neighborhood is
not itself open. -/
theorem exists_refinement_in_nhds {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (t : ℝ) (ht : t ∈ Ioo C.a C.b)
    (V : Set Plane) (hV : V ∈ 𝓝 ((t, 0) : Plane)) :
    ∃ D : CommonCollar L₁ L₂ w, t ∈ Ioo D.a D.b ∧
      rectangle D.a D.b D.r ⊆ rectangle C.a C.b C.r ∩ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨D, htD, hD⟩ := exists_refinement_in_open C t ht
    (Metric.ball (t, 0) ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  refine ⟨D, htD, ?_⟩
  intro p hp
  exact ⟨(hD hp).1, hball (hD hp).2⟩

end MNEC.CollarRefinements
