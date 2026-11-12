module

public import VeechDichotomy.NativeVeech
public import VeechDichotomy.Configuration
public import VeechDichotomy.MarkedOrbit

/-! The group of actual affine automorphisms of a native compact
translation surface, its derivative homomorphism, and its continuous
action on points. This connects the abstract configuration lemmas to
genuine holomorphic differentials and their regular translation charts.
-/

@[expose] public section

noncomputable section

namespace VeechDichotomy.NativeAffineGroup

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech LinearGroup Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev Raw (q : Differential X) :=
  (X ≃ₜ X) × ((Regular q ≃ₜ Regular q) × SL2)

def asRaw {q : Differential X} {A : SL2} (e : AffineAutomorphism q A) : Raw q :=
  (e.surface, e.regular, A)

def affineSubgroup (q : Differential X) : Subgroup (Raw q) where
  carrier := {r | ∃ (A : SL2) (e : AffineAutomorphism q A), asRaw e = r}
  one_mem' := ⟨1, AffineAutomorphism.identity q, rfl⟩
  mul_mem' := by
    rintro r s ⟨A, e, rfl⟩ ⟨B, f, rfl⟩
    exact ⟨A * B, AffineAutomorphism.multiply q e f, rfl⟩
  inv_mem' := by
    rintro r ⟨A, e, rfl⟩
    exact ⟨A⁻¹, AffineAutomorphism.inverse q e, rfl⟩

abbrev AffineGroup (q : Differential X) := affineSubgroup q

def derivative (q : Differential X) : AffineGroup q →* SL2 where
  toFun a := a.val.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

def pointHomeomorph (q : Differential X) : AffineGroup q →* (X ≃ₜ X) where
  toFun a := a.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

instance action (q : Differential X) : MulAction (AffineGroup q) X where
  smul a x := pointHomeomorph q a x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance continuousConstSMul (q : Differential X) :
    ContinuousConstSMul (AffineGroup q) X where
  continuous_const_smul a := (pointHomeomorph q a).continuous

theorem derivative_range (q : Differential X) :
    (derivative q).range = NativeVeech.derivativeGroup q := by
  ext A
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨B, e, he⟩ := a.property
    have hB : B = derivative q a := congrArg (fun r : Raw q => r.2.2) he
    rw [← hB]
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨⟨asRaw e, A, e, rfl⟩, rfl⟩

/-- The orbit-closure criterion for the actual native affine group. -/
theorem compact_configuration_iff (q : Differential X) {m : ℕ} (b : Fin m → X) :
    (∃ F : Set (Fin m → X), IsCompact F ∧ invariant (AffineGroup q) F ∧
      b ∈ F ∧ F ⊆ configuration m X) ↔
      Disjoint (closure (MulAction.orbit (AffineGroup q) b)) (fatDiagonal m X) :=
  compact_configuration_iff_orbitClosure_avoids_diagonal b

end VeechDichotomy.NativeAffineGroup
