module

public import VeechDichotomy.NativeCoverMonodromyClassification
public import VeechDichotomy.NativeDifferentialEquivalenceLaws
public import VeechDichotomy.FiniteMonodromyRepresentations
public import VeechDichotomy.FiniteClassifyingMap

/-! The monodromy argument bounds actual native cover-isomorphism classes
in any family over a fixed pointed base with fixed degree. The separate
finite-generation theorem for the punctured fundamental group remains
explicit; it is neither postulated nor hidden in cover data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverFamilyFiniteness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeRelativePuncturedCover
open Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))

def Equivalent (i j : ι) : Prop :=
  ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY i) (ωY j), ∀ y, (π j).map (e.homeomorph y) = (π i).map y

def coverSetoid : Setoid ι where
  r := Equivalent Y ωY π
  iseqv := by
    constructor
    · intro i
      exact ⟨NativeDifferentialEquivalenceLaws.refl (ωY i), fun _ => rfl⟩
    · rintro i j ⟨e, he⟩
      refine ⟨NativeDifferentialEquivalenceLaws.symm e, ?_⟩
      intro z
      change (π i).map (e.homeomorph.symm z) = (π j).map z
      simpa only [Homeomorph.apply_symm_apply] using (he (e.homeomorph.symm z)).symm
    · rintro i j k ⟨e, he⟩ ⟨f, hf⟩
      refine ⟨NativeDifferentialEquivalenceLaws.trans e f, ?_⟩
      intro y
      exact (hf (e.homeomorph y)).trans (he y)

def labeling {B : Set X} (x : base B) {d : ℕ}
    (hcard : ∀ i, Nat.card (map (π i) B ⁻¹' {x}) = d) (i : ι) :
    (map (π i) B ⁻¹' {x}) ≃ Fin d := by
  let : Finite (map (π i) B ⁻¹' {x}) := fiber_finite (π i) B x
  exact Finite.equivFinOfCardEq (hcard i)

def classifyingMap {B : Set X} (hbranch : ∀ i, branchValues (π i) ⊆ B)
    (x : base B) {d : ℕ} (hcard : ∀ i, Nat.card (map (π i) B ⁻¹' {x}) = d) (i : ι) :
    FundamentalGroup (base B) x →* Equiv.Perm (Fin d) :=
  NumberedCoverMonodromy.representation (isCoveringMap (π i) (hbranch i)) (labeling Y ωY π x hcard i)

theorem finite_classes {B : Set X} (hB : B.Finite) (hbranch : ∀ i, branchValues (π i) ⊆ B)
    (x : base B) {d : ℕ} (hcard : ∀ i, Nat.card (map (π i) B ⁻¹' {x}) = d)
    (hfg : Group.FG (FundamentalGroup (base B) x)) : Finite (Quotient (coverSetoid Y ωY π)) := by
  let : Finite (FundamentalGroup (base B) x →* Equiv.Perm (Fin d)) :=
    FiniteMonodromyRepresentations.finite_homs_of_fg hfg
  apply FiniteClassifyingMap.finite_quotient (coverSetoid Y ωY π) (classifyingMap Y ωY π hbranch x hcard)
  intro i j heq
  exact NativeCoverMonodromyClassification.exists_equivalence_of_numbered_eq
    (π i) (π j) hB (hbranch i) (hbranch j) x (labeling Y ωY π x hcard i) (labeling Y ωY π x hcard j) heq

end VeechDichotomy.NativeCoverFamilyFiniteness
