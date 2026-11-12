module

public import MNEC.SeamClasses

@[expose] public section

/-!
# Classification of regular points in the actual slit quotient

Every quotient point is represented by an off-slit torus point, an interior
bank point, or one of the two endpoints. For embedded slits the interior
bank points are distinct from the endpoints. No Hausdorffness or closedness
of the endpoint set is assumed here.
-/

noncomputable section

namespace MNEC.RegularPoints

open LatticeTorus CutTorus SlitConnectedSum OffSlitEmbeddings CutBankLifts Set
open scoped Classical

def initialPoint (L₁ L₂ : Lattice) (w : Plane) : Surface L₁ L₂ w :=
  left L₁ L₂ w (upper L₁ w (L₁.project 0))

def terminalPoint (L₁ L₂ : Lattice) (w : Plane) : Surface L₁ L₂ w :=
  left L₁ L₂ w (upper L₁ w (L₁.project w))

def endpointSet (L₁ L₂ : Lattice) (w : Plane) : Set (Surface L₁ L₂ w) :=
  {initialPoint L₁ L₂ w, terminalPoint L₁ L₂ w}

def regularSet (L₁ L₂ : Lattice) (w : Plane) : Set (Surface L₁ L₂ w) :=
  (endpointSet L₁ L₂ w)ᶜ

def interiorPoint (L₁ L₂ : Lattice) (w : Plane) (t : ℝ)
    (ht : 0 < t ∧ t < 1) (k : Bool) : Surface L₁ L₂ w :=
  left L₁ L₂ w (interiorBank L₁ w k t ht)

theorem endpoints_distinct (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    initialPoint L₁ L₂ w ≠ terminalPoint L₁ L₂ w :=
  SeamClasses.initial_ne_terminal L₁ L₂ w hw₁ hw₂

theorem cut_point_classification (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (q : Point L w) :
    q = upper L w (L.project 0) ∨ q = upper L w (L.project w) ∨
      (∃ x : OffSlit L w, q = normalLift L w x) ∨
      ∃ (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool), q = interiorBank L w k t ht := by
  by_cases hslit : base q ∈ L.slitSet w
  · obtain ⟨t, htq⟩ := hslit
    by_cases ht0 : (t : ℝ) = 0
    · apply Or.inl
      have hbase : base q = L.project 0 := by
        simpa [Lattice.arc, ht0] using htq.symm
      apply endpoint_unique L w hw q (upper L w (L.project 0))
      · rw [hbase]
        exact Or.inl rfl
      · exact hbase
    · by_cases ht1 : (t : ℝ) = 1
      · apply Or.inr ∘ Or.inl
        have hbase : base q = L.project w := by
          simpa [Lattice.arc, ht1] using htq.symm
        apply endpoint_unique L w hw q (upper L w (L.project w))
        · rw [hbase]
          exact Or.inr (Set.mem_singleton_iff.mpr rfl)
        · exact hbase
      · apply Or.inr ∘ Or.inr ∘ Or.inr
        have ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
        refine ⟨t, ht, bank q, ?_⟩
        exact point_ext (p := q) (q := interiorBank L w (bank q) t ht) htq.symm rfl
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    let x : OffSlit L w := ⟨base q, hslit⟩
    refine ⟨x, ?_⟩
    apply point_ext (p := q) (q := normalLift L w x) rfl
    exact bank_false_off_interior q (fun hi => hslit (interior_subset_slit L w hi))

theorem right_interior_eq_left_opposite (L₁ L₂ : Lattice) (w : Plane)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool) :
    right L₁ L₂ w (interiorBank L₂ w k t ht) = interiorPoint L₁ L₂ w t ht (!k) := by
  cases k
  · exact (lower_upper_glued L₁ L₂ w t ht.1 ht.2).symm
  · exact (upper_lower_glued L₁ L₂ w t ht.1 ht.2).symm

/-- Exhaustive classification using the two actual cut-torus representatives. -/
theorem point_classification (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (p : Surface L₁ L₂ w) :
    p = initialPoint L₁ L₂ w ∨ p = terminalPoint L₁ L₂ w ∨
      p ∈ range (leftOff L₁ L₂ w) ∨ p ∈ range (rightOff L₁ L₂ w) ∨
      ∃ (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool), p = interiorPoint L₁ L₂ w t ht k := by
  refine Quotient.inductionOn p (fun raw => ?_)
  cases raw with
  | inl q =>
      rcases cut_point_classification L₁ w hw₁ q with h | h | ⟨x, h⟩ | ⟨t, ht, k, h⟩
      · exact Or.inl (congrArg (left L₁ L₂ w) h)
      · exact Or.inr (Or.inl (congrArg (left L₁ L₂ w) h))
      · exact Or.inr (Or.inr (Or.inl ⟨x, (congrArg (left L₁ L₂ w) h).symm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht, k, congrArg (left L₁ L₂ w) h⟩)))
  | inr q =>
      rcases cut_point_classification L₂ w hw₂ q with h | h | ⟨x, h⟩ | ⟨t, ht, k, h⟩
      · exact Or.inl ((congrArg (right L₁ L₂ w) h).trans (initial_glued L₁ L₂ w).symm)
      · exact Or.inr (Or.inl
          ((congrArg (right L₁ L₂ w) h).trans (terminal_glued L₁ L₂ w).symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨x, (congrArg (right L₁ L₂ w) h).symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht, !k,
          (congrArg (right L₁ L₂ w) h).trans
            (right_interior_eq_left_opposite L₁ L₂ w t ht k)⟩)))

@[simp] theorem offTrace_initialPoint (L₁ L₂ : Lattice) (w : Plane) :
    offTrace L₁ L₂ w (initialPoint L₁ L₂ w) = none := by
  change (if L₁.project 0 ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project 0))) = none
  apply ite_eq_left
  exact ⟨⟨0, by constructor <;> norm_num⟩, by simp [Lattice.arc]⟩

@[simp] theorem offTrace_terminalPoint (L₁ L₂ : Lattice) (w : Plane) :
    offTrace L₁ L₂ w (terminalPoint L₁ L₂ w) = none := by
  change (if L₁.project w ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project w))) = none
  apply ite_eq_left
  exact ⟨⟨1, by constructor <;> norm_num⟩, by simp [Lattice.arc]⟩

theorem leftOff_mem_regular (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₁ w) :
    leftOff L₁ L₂ w p ∈ regularSet L₁ L₂ w := by
  rintro (h | h)
  · have heq := congrArg (offTrace L₁ L₂ w) h
    simp only [offTrace_leftOff, offTrace_initialPoint] at heq
    cases heq
  · have heq := congrArg (offTrace L₁ L₂ w) (Set.mem_singleton_iff.mp h)
    simp only [offTrace_leftOff, offTrace_terminalPoint] at heq
    cases heq

theorem rightOff_mem_regular (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₂ w) :
    rightOff L₁ L₂ w p ∈ regularSet L₁ L₂ w := by
  rintro (h | h)
  · have heq := congrArg (offTrace L₁ L₂ w) h
    simp only [offTrace_rightOff, offTrace_initialPoint] at heq
    cases heq
  · have heq := congrArg (offTrace L₁ L₂ w) (Set.mem_singleton_iff.mp h)
    simp only [offTrace_rightOff, offTrace_terminalPoint] at heq
    cases heq

theorem interiorPoint_ne_initial (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool) :
    interiorPoint L₁ L₂ w t ht k ≠ initialPoint L₁ L₂ w := by
  intro h
  have hb := congrArg base (SeamClasses.left_injective L₁ L₂ w hw₁ hw₂ h)
  have heq : L₁.arc w ⟨t, ht.1.le, ht.2.le⟩ =
      L₁.arc w ⟨0, by constructor <;> norm_num⟩ := by
    simpa [Lattice.arc] using hb
  have ht0 := congrArg Subtype.val (hw₁ heq)
  exact ht.1.ne' ht0

theorem interiorPoint_ne_terminal (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool) :
    interiorPoint L₁ L₂ w t ht k ≠ terminalPoint L₁ L₂ w := by
  intro h
  have hb := congrArg base (SeamClasses.left_injective L₁ L₂ w hw₁ hw₂ h)
  have heq : L₁.arc w ⟨t, ht.1.le, ht.2.le⟩ =
      L₁.arc w ⟨1, by constructor <;> norm_num⟩ := by
    simpa [Lattice.arc] using hb
  have ht1 := congrArg Subtype.val (hw₁ heq)
  exact ht.2.ne ht1

theorem interiorPoint_mem_regular (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool) :
    interiorPoint L₁ L₂ w t ht k ∈ regularSet L₁ L₂ w := by
  rintro (h | h)
  · exact interiorPoint_ne_initial L₁ L₂ w hw₁ hw₂ t ht k h
  · exact interiorPoint_ne_terminal L₁ L₂ w hw₁ hw₂ t ht k (Set.mem_singleton_iff.mp h)

theorem regular_classification (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (p : Surface L₁ L₂ w) (hp : p ∈ regularSet L₁ L₂ w) :
    p ∈ range (leftOff L₁ L₂ w) ∨ p ∈ range (rightOff L₁ L₂ w) ∨
      ∃ (t : ℝ) (ht : 0 < t ∧ t < 1) (k : Bool), p = interiorPoint L₁ L₂ w t ht k := by
  rcases point_classification L₁ L₂ w hw₁ hw₂ p with h | h | h | h | h
  · exact False.elim (hp (Or.inl h))
  · exact False.elim (hp (Or.inr (Set.mem_singleton_iff.mpr h)))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end MNEC.RegularPoints
