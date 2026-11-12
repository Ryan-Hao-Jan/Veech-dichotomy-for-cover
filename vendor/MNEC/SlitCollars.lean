module

public import MNEC.OffSlitEmbeddings
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Constructed physical collars for arbitrary lattice slits

The quotient charts use each lattice's actual inverse frame. Compactness of
the remote part of an embedded slit then isolates one straight subarc. The
resulting rectangular collars and common two-torus collars are proved to
exist; no collar or surface classification is assumed.

The compact-isolation and rectangle-shrinking arguments adapt the user's
earlier geometric slit library, with no imports from CriticalMeasure.
-/

noncomputable section

namespace MNEC.SlitCollars

open LatticeTorus CutTorus OffSlitEmbeddings Set Topology
open scoped Classical

def coordinateTorusChart (a : Plane) : OpenPartialHomeomorph Plane Torus :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a.1).prod
    (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a.2)

/-- A physical-plane quotient chart for the specified arbitrary lattice. -/
def torusChart (L : Lattice) (a : Plane) : OpenPartialHomeomorph Plane Torus :=
  L.frame.symm.toHomeomorph.transOpenPartialHomeomorph (coordinateTorusChart a)

theorem torusChart_apply (L : Lattice) (a p : Plane) : torusChart L a p = L.project p := rfl

theorem torusChart_source (L : Lattice) (a : Plane) :
    (torusChart L a).source =
      L.frame.symm ⁻¹' (Ioo a.1 (a.1 + 1) ×ˢ Ioo a.2 (a.2 + 1)) := rfl

def chartOrigin (L : Lattice) (p : Plane) : Plane :=
  ((L.frame.symm p).1 - 1 / 2, (L.frame.symm p).2 - 1 / 2)

theorem mem_center_chart (L : Lattice) (p : Plane) :
    p ∈ (torusChart L (chartOrigin L p)).source := by
  rw [torusChart_source]
  dsimp only [Set.mem_preimage, Set.mem_prod, chartOrigin]
  constructor <;> constructor <;> linarith

theorem projection_injOn_chart (L : Lattice) (a : Plane) :
    InjOn L.project (torusChart L a).source := (torusChart L a).injOn

theorem projection_image_open_in_chart (L : Lattice) (a : Plane) (U : Set Plane)
    (hU : IsOpen U) (hsub : U ⊆ (torusChart L a).source) : IsOpen (L.project '' U) :=
  (torusChart L a).isOpen_image_of_subset_source hU hsub

/-- Compactness of the remote subarc isolates any open parameter interval. -/
theorem local_parameter_isolation (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (t : Parameter) (a b : ℝ) (ht : (t : ℝ) ∈ Ioo a b) :
    ∃ O : Set Torus, IsOpen O ∧ L.arc w t ∈ O ∧
      ∀ s : Parameter, L.arc w s ∈ O → (s : ℝ) ∈ Ioo a b := by
  let K : Set Parameter := {s | (s : ℝ) ∉ Ioo a b}
  have hK : IsClosed K :=
    (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.preimage continuous_subtype_val
  have hclosed : IsClosed (L.arc w '' K) :=
    (hK.isCompact.image (L.continuous_arc w)).isClosed
  have hnot : L.arc w t ∉ L.arc w '' K := by
    rintro ⟨s, hs, hst⟩
    have heq := hw hst
    subst s
    exact hs ht
  refine ⟨(L.arc w '' K)ᶜ, hclosed.isOpen_compl, hnot, ?_⟩
  intro s hs
  by_contra hn
  exact hs ⟨s, hn, rfl⟩

theorem exists_parameter_interval_in_chart (L : Lattice) (w : Plane) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, a < t ∧ t < b ∧ Ioo a b ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ s ∈ Ioo a b, s • w ∈ (torusChart L (chartOrigin L (t • w))).source := by
  let U : Set ℝ := Ioo (0 : ℝ) 1 ∩
    (fun s : ℝ => s • w) ⁻¹' (torusChart L (chartOrigin L (t • w))).source
  have hc : Continuous (fun s : ℝ => s • w) := continuous_id.smul continuous_const
  have hU : IsOpen U := isOpen_Ioo.inter ((torusChart L _).open_source.preimage hc)
  have htU : t ∈ U := ⟨ht, mem_center_chart L (t • w)⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU t htU
  refine ⟨t - r, t + r, by linarith only [hr], by linarith only [hr], ?_, ?_⟩
  · intro s hs
    apply (hball ?_).1
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  · intro s hs
    apply (hball ?_).2
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩

/-- A small actual physical ball sees the entire slit as one straight local
subarc and has no other lattice translate entering its quotient chart. -/
theorem exists_straight_slit_ball (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ a b r : ℝ, a < t ∧ t < b ∧ 0 < r ∧ Ioo a b ⊆ Ioo (0 : ℝ) 1 ∧
      InjOn L.project (Metric.ball (t • w) r) ∧
      ∀ p ∈ Metric.ball (t • w) r,
        (L.project p ∈ L.slitSet w ↔ ∃ s ∈ Ioo a b, p = s • w) := by
  obtain ⟨a, b, hat, htb, hinterval, hchart⟩ :=
    exists_parameter_interval_in_chart L w t ht
  let ti : Parameter := ⟨t, ht.1.le, ht.2.le⟩
  obtain ⟨O, hO, htO, hisolate⟩ :=
    local_parameter_isolation L w hw ti a b ⟨hat, htb⟩
  let P : Set Plane :=
    (torusChart L (chartOrigin L (t • w))).source ∩ L.project ⁻¹' O
  have hP : IsOpen P :=
    (torusChart L _).open_source.inter (hO.preimage L.continuous_project)
  have htP : t • w ∈ P := ⟨mem_center_chart L _, htO⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hP (t • w) htP
  refine ⟨a, b, r, hat, htb, hr, hinterval,
    (projection_injOn_chart L _).mono (fun _ hp => (hball hp).1), ?_⟩
  intro p hp
  constructor
  · rintro ⟨s, hs⟩
    have hsO : L.arc w s ∈ O := hs ▸ (hball hp).2
    have hsI := hisolate s hsO
    refine ⟨s, hsI, ?_⟩
    exact projection_injOn_chart L _ (hball hp).1 (hchart s hsI) hs.symm
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, (hinterval hs).1.le, (hinterval hs).2.le⟩, rfl⟩

def rectangle (a b r : ℝ) : Set Plane := Ioo a b ×ˢ Ioo (-r) r

/-- Physical rectangular data, with its geometric properties verified below
by an existence theorem for every embedded slit and interior parameter. -/
structure Collar (L : Lattice) (w : Plane) where
  a : ℝ
  b : ℝ
  r : ℝ
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_one : b < 1
  r_pos : 0 < r
  projection_injective : InjOn (fun p => L.project (frame w p)) (rectangle a b r)
  slit_iff : ∀ p ∈ rectangle a b r, L.project (frame w p) ∈ L.slitSet w ↔ p.2 = 0

def domain {L : Lattice} {w : Plane} (C : Collar L w) : Set Plane :=
  rectangle C.a C.b C.r

theorem domain_open {L : Lattice} {w : Plane} (C : Collar L w) : IsOpen (domain C) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem domain_longitudinal {L : Lattice} {w : Plane} (C : Collar L w)
    {p : Plane} (hp : p ∈ domain C) : p.1 ∈ Ioo (0 : ℝ) 1 :=
  ⟨C.a_pos.trans hp.1.1, hp.1.2.trans C.b_lt_one⟩

theorem frame_zero_normal (w : Plane) (s : ℝ) : frame w (s, 0) = s • w := by
  simp [frame]

theorem zero_normal_on_slit {L : Lattice} {w : Plane} (C : Collar L w)
    {p : Plane} (hp : p ∈ domain C) :
    L.project (frame w p) ∈ L.slitSet w ↔ p.2 = 0 := C.slit_iff p hp

theorem exists_collar_at (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ∃ C : Collar L w, t ∈ Ioo C.a C.b := by
  obtain ⟨a₀, b₀, R, hat, htb, hR, hJ, hinj, hslit⟩ :=
    exists_straight_slit_ball L w hw t ht
  have hnz := embeddedSlit_ne_zero L w hw
  let P : Set Plane := frame w ⁻¹' Metric.ball (t • w) R
  have hP : IsOpen P :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (t • w) R)).preimage (continuous_frame w)
  have hcenter : ((t, 0) : Plane) ∈ P := by
    change frame w (t, 0) ∈ Metric.ball (t • w) R
    rw [frame_zero_normal]
    exact Metric.mem_ball_self hR
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hP (t, 0) hcenter
  let ρ := min (ε / 2) (min (t / 2) ((1 - t) / 2))
  have hρ : 0 < ρ :=
    lt_min (by positivity) (lt_min (by linarith only [ht.1]) (by linarith only [ht.2]))
  have hρε : ρ ≤ ε / 2 := min_le_left _ _
  have hρt : ρ ≤ t / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ1 : ρ ≤ (1 - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρε' : ρ < ε := hρε.trans_lt (by linarith only [hε])
  have hinside : ∀ p ∈ rectangle (t - ρ) (t + ρ) ρ,
      frame w p ∈ Metric.ball (t • w) R := by
    intro p hp
    apply hball
    rw [← ball_prod_same]
    constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr
        ⟨by linarith only [hp.1.1, hρε'], by linarith only [hp.1.2, hρε']⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact abs_lt.mpr
        ⟨by linarith only [hp.2.1, hρε'], by linarith only [hp.2.2, hρε']⟩
  let C : Collar L w := {
    a := t - ρ
    b := t + ρ
    r := ρ
    a_pos := by linarith only [ht.1, hρt]
    a_lt_b := by linarith only [hρ]
    b_lt_one := by linarith only [ht.2, hρ1]
    r_pos := hρ
    projection_injective := by
      intro p hp q hq heq
      apply (frameHomeomorph w hnz).injective
      exact hinj (hinside p hp) (hinside q hq) heq
    slit_iff := by
      intro p hp
      constructor
      · intro hcut
        obtain ⟨s, hs, heq⟩ := (hslit (frame w p) (hinside p hp)).mp hcut
        have hframe : frame w p = frame w (s, 0) :=
          heq.trans (frame_zero_normal w s).symm
        exact congrArg Prod.snd ((frameHomeomorph w hnz).injective hframe)
      · intro hz
        have heq : p = (p.1, 0) := Prod.ext rfl hz
        rw [heq, frame_zero_normal]
        refine ⟨⟨p.1, ?_, ?_⟩, rfl⟩
        · linarith only [hp.1.1, ht.1, hρt]
        · linarith only [hp.1.2, ht.2, hρ1]
  }
  exact ⟨C, by change t - ρ < t ∧ t < t + ρ; constructor <;> linarith only [hρ]⟩

def localCollar (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Collar L w :=
  (exists_collar_at L w hw t ht).choose

theorem mem_localCollar (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ∈ Ioo (localCollar L w hw t ht).a (localCollar L w hw t ht).b :=
  (exists_collar_at L w hw t ht).choose_spec

theorem projected_domain_open {L : Lattice} {w : Plane} (C : Collar L w) (hw : w ≠ 0) :
    IsOpen ((fun p => L.project (frame w p)) '' domain C) := by
  rw [← Set.image_image]
  exact L.isOpenMap_project _ ((frameHomeomorph w hw).isOpenMap _ (domain_open C))

/-- Shared physical bounds for a collar that works in both unrelated tori. -/
structure CommonCollar (L₁ L₂ : Lattice) (w : Plane) where
  a : ℝ
  b : ℝ
  r : ℝ
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_one : b < 1
  r_pos : 0 < r
  left_injective : InjOn (fun p => L₁.project (frame w p)) (rectangle a b r)
  right_injective : InjOn (fun p => L₂.project (frame w p)) (rectangle a b r)
  left_slit_iff : ∀ p ∈ rectangle a b r, L₁.project (frame w p) ∈ L₁.slitSet w ↔ p.2 = 0
  right_slit_iff : ∀ p ∈ rectangle a b r, L₂.project (frame w p) ∈ L₂.slitSet w ↔ p.2 = 0

def CommonCollar.leftCollar {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) : Collar L₁ w :=
  ⟨C.a, C.b, C.r, C.a_pos, C.a_lt_b, C.b_lt_one, C.r_pos,
    C.left_injective, C.left_slit_iff⟩

def CommonCollar.rightCollar {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) : Collar L₂ w :=
  ⟨C.a, C.b, C.r, C.a_pos, C.a_lt_b, C.b_lt_one, C.r_pos,
    C.right_injective, C.right_slit_iff⟩

theorem exists_common_collar_at (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ C : CommonCollar L₁ L₂ w, t ∈ Ioo C.a C.b := by
  obtain ⟨C₁, ht₁⟩ := exists_collar_at L₁ w hw₁ t ht
  obtain ⟨C₂, ht₂⟩ := exists_collar_at L₂ w hw₂ t ht
  let a := max C₁.a C₂.a
  let b := min C₁.b C₂.b
  let r := min C₁.r C₂.r
  have hat : a < t := max_lt ht₁.1 ht₂.1
  have htb : t < b := lt_min ht₁.2 ht₂.2
  have hsub₁ : rectangle a b r ⊆ domain C₁ := by
    intro p hp
    have ha : C₁.a ≤ a := le_max_left _ _
    have hb : b ≤ C₁.b := min_le_left _ _
    have hr : r ≤ C₁.r := min_le_left _ _
    exact ⟨⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩,
      ⟨by linarith only [hp.2.1, hr], hp.2.2.trans_le hr⟩⟩
  have hsub₂ : rectangle a b r ⊆ domain C₂ := by
    intro p hp
    have ha : C₂.a ≤ a := le_max_right _ _
    have hb : b ≤ C₂.b := min_le_right _ _
    have hr : r ≤ C₂.r := min_le_right _ _
    exact ⟨⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩,
      ⟨by linarith only [hp.2.1, hr], hp.2.2.trans_le hr⟩⟩
  refine ⟨{
    a := a
    b := b
    r := r
    a_pos := C₁.a_pos.trans_le (le_max_left _ _)
    a_lt_b := hat.trans htb
    b_lt_one := (min_le_left _ _).trans_lt C₁.b_lt_one
    r_pos := lt_min C₁.r_pos C₂.r_pos
    left_injective := C₁.projection_injective.mono hsub₁
    right_injective := C₂.projection_injective.mono hsub₂
    left_slit_iff := fun p hp => C₁.slit_iff p (hsub₁ hp)
    right_slit_iff := fun p hp => C₂.slit_iff p (hsub₂ hp)
  }, hat, htb⟩

def commonLocalCollar (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : CommonCollar L₁ L₂ w :=
  (exists_common_collar_at L₁ L₂ w hw₁ hw₂ t ht).choose

theorem mem_commonLocalCollar (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ∈ Ioo (commonLocalCollar L₁ L₂ w hw₁ hw₂ t ht).a
      (commonLocalCollar L₁ L₂ w hw₁ hw₂ t ht).b :=
  (exists_common_collar_at L₁ L₂ w hw₁ hw₂ t ht).choose_spec

end MNEC.SlitCollars
