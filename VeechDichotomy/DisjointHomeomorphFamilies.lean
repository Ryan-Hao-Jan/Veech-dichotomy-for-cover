module

public import VeechDichotomy.DisjointPointTransport

/-! Finite composition of continuous families with fixed disjoint supports.
The parameter space is arbitrary, allowing both the complex structure and
the point displacements to vary in a single family. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DisjointHomeomorphFamilies

open Set

variable {X P ι : Type*} [TopologicalSpace X] [TopologicalSpace P]

theorem exists_family (K : ι → Set X) (F : ι → P → X ≃ₜ X)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hforward : ∀ i, Continuous (fun p : P × X => F i p.1 p.2))
    (hinverse : ∀ i, Continuous (fun p : P × X => (F i p.1).symm p.2))
    (hfix : ∀ i p x, x ∉ K i → F i p x = x) (T : Finset ι) :
    ∃ G : P → X ≃ₜ X,
      Continuous (fun p : P × X => G p.1 p.2) ∧
      Continuous (fun p : P × X => (G p.1).symm p.2) ∧
      (∀ i ∈ T, ∀ p x, x ∈ K i → G p x = F i p x) ∧
      (∀ i ∉ T, ∀ p x, x ∈ K i → G p x = x) ∧
      (∀ p x, (∀ i ∈ T, x ∉ K i) → G p x = x) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => Homeomorph.refl X, continuous_snd, continuous_snd, ?_, ?_, ?_⟩
    · intro i hi
      simp at hi
    · intro i _ p x _
      rfl
    · intro p x _
      rfl
  | @insert a T haT ih =>
    obtain ⟨G, hG, hInv, hown, hother, hfixed⟩ := ih
    let H : P → X ≃ₜ X := fun p => (G p).trans (F a p)
    have hH : Continuous (fun p : P × X => H p.1 p.2) :=
      (hforward a).comp (continuous_fst.prodMk hG)
    have hHInv : Continuous (fun p : P × X => (H p.1).symm p.2) :=
      hInv.comp (continuous_fst.prodMk (hinverse a))
    refine ⟨H, hH, hHInv, ?_, ?_, ?_⟩
    · intro i hi p x hx
      change F a p (G p x) = F i p x
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst i
        rw [hother a haT p x hx]
      · have hai : a ≠ i := by
          intro h
          subst i
          exact haT hi
        have hnot : F i p x ∉ K a := fun ha =>
          disjoint_left.mp (hdisj hai) ha
            (DisjointPointTransport.mapsTo_of_fixed (F i p) (hfix i p) hx)
        rw [hown i hi p x hx, hfix a p _ hnot]
    · intro i hi p x hx
      have hiT : i ∉ T := fun hit => hi (Finset.mem_insert_of_mem hit)
      have hai : a ≠ i := by
        intro h
        subst i
        exact hi (by simp)
      have hnot : x ∉ K a := fun ha => disjoint_left.mp (hdisj hai) ha hx
      change F a p (G p x) = x
      rw [hother i hiT p x hx, hfix a p x hnot]
    · intro p x hx
      have hrest : ∀ i ∈ T, x ∉ K i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      change F a p (G p x) = x
      rw [hfixed p x hrest]
      exact hfix a p x (hx a (by simp))

theorem exists_all [Finite ι] (K : ι → Set X) (F : ι → P → X ≃ₜ X)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hforward : ∀ i, Continuous (fun p : P × X => F i p.1 p.2))
    (hinverse : ∀ i, Continuous (fun p : P × X => (F i p.1).symm p.2))
    (hfix : ∀ i p x, x ∉ K i → F i p x = x) :
    ∃ G : P → X ≃ₜ X,
      Continuous (fun p : P × X => G p.1 p.2) ∧
      Continuous (fun p : P × X => (G p.1).symm p.2) ∧
      (∀ i p x, x ∈ K i → G p x = F i p x) ∧
      (∀ p x, (∀ i, x ∉ K i) → G p x = x) := by
  let := Fintype.ofFinite ι
  obtain ⟨G, hG, hInv, hown, _, hfixed⟩ :=
    exists_family K F hdisj hforward hinverse hfix Finset.univ
  exact ⟨G, hG, hInv, fun i => hown i (Finset.mem_univ i),
    fun p x hx => hfixed p x (fun i _ => hx i)⟩

omit [TopologicalSpace P] in
theorem inverse_restriction (K : ι → Set X) (F : ι → P → X ≃ₜ X)
    (hfix : ∀ i p x, x ∉ K i → F i p x = x) (G : P → X ≃ₜ X)
    (hown : ∀ i p x, x ∈ K i → G p x = F i p x)
    (p : P) (i : ι) {x : X} (hx : x ∈ K i) :
    (G p).symm x = (F i p).symm x := by
  let y := (F i p).symm x
  have hfixInv : ∀ z ∉ K i, (F i p).symm z = z := by
    intro z hz
    apply (F i p).injective
    rw [(F i p).apply_symm_apply, hfix i p z hz]
  have hy : y ∈ K i := DisjointPointTransport.mapsTo_of_fixed (F i p).symm hfixInv hx
  have heq : G p y = x := (hown i p y hy).trans ((F i p).apply_symm_apply x)
  calc
    (G p).symm x = (G p).symm (G p y) := congrArg (G p).symm heq.symm
    _ = y := (G p).symm_apply_apply y

end VeechDichotomy.DisjointHomeomorphFamilies
