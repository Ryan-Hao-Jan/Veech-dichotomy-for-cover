module

public import VeechDichotomy.Configuration
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Algebra.Group.Basic

/-! The compact-configuration part of the torsion corollary, using actual
torsion points in a topological additive group. This does not assume that
the torus map of a translation surface or its affine equivariance has
already been constructed.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

variable {X E : Type*} {m : ℕ}

def torsionPoints (N : ℕ) (E : Type*) [AddMonoid E] : Set E :=
  {t | N • t = 0}

def torsionSeparated [AddGroup E] (f : X → E) (N : ℕ) : Set (Fin m → X) :=
  {b | ∀ i j, i ≠ j → N • (f (b j) - f (b i)) = 0 ∧ f (b j) - f (b i) ≠ 0}

theorem torsionSeparated_subset_configuration [AddGroup E] (f : X → E) (N : ℕ) :
    torsionSeparated (m := m) f N ⊆ configuration m X := by
  intro b hb i j hij
  by_contra hne
  have h := (hb i j hne).2
  rw [hij, sub_self] at h
  exact h rfl

section Topology

variable [TopologicalSpace X] [CompactSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]

omit [CompactSpace X] in
theorem isClosed_torsionSeparated {f : X → E} (hf : Continuous f) {N : ℕ}
    (hT : (torsionPoints N E).Finite) :
    IsClosed (torsionSeparated (m := m) f N) := by
  have hclosed : IsClosed (torsionPoints N E \ {0}) :=
    hT.sdiff.isClosed
  have heq : torsionSeparated (m := m) f N =
      ⋂ i : Fin m, ⋂ j : Fin m, ⋂ (_ : i ≠ j),
        (fun b : Fin m → X => f (b j) - f (b i)) ⁻¹' (torsionPoints N E \ {0}) := by
    ext b
    simp [torsionSeparated, torsionPoints]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    hclosed.preimage ((hf.comp (continuous_apply j)).sub (hf.comp (continuous_apply i)))

theorem isCompact_torsionSeparated {f : X → E} (hf : Continuous f) {N : ℕ}
    (hT : (torsionPoints N E).Finite) :
    IsCompact (torsionSeparated (m := m) f N) :=
  (isClosed_torsionSeparated hf hT).isCompact

end Topology

section AffineAction

variable {G : Type*} [Group G] [MulAction G X] [AddCommGroup E]

/-- Cancellation of the translation term in an affine transformation. -/
theorem affine_difference (ρ : E ≃+ E) (c x y : E) :
    (ρ y + c) - (ρ x + c) = ρ (y - x) := by
  simp only [add_sub_add_right_eq_sub, map_sub]

theorem invariant_torsionSeparated
    (f : X → E) (N : ℕ) (ρ : G → E ≃+ E) (c : G → E)
    (hequiv : ∀ g x, f (g • x) = ρ g (f x) + c g) :
    invariant G (torsionSeparated (m := m) f N) := by
  intro g b hb i j hij
  change N • (f (g • b j) - f (g • b i)) = 0 ∧
    f (g • b j) - f (g • b i) ≠ 0
  rw [hequiv, hequiv, affine_difference]
  constructor
  · rw [← map_nsmul, (hb i j hij).1, map_zero]
  · intro heq
    apply (hb i j hij).2
    exact (ρ g).injective (heq.trans (map_zero (ρ g)).symm)

variable [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]

/-- Every torsion-separated tuple belongs to an explicitly constructed
compact invariant subset of the distinct-configuration locus. -/
theorem torsionSeparated_compact_configuration
    {f : X → E} (hf : Continuous f) {N : ℕ}
    (hT : (torsionPoints N E).Finite) (ρ : G → E ≃+ E) (c : G → E)
    (hequiv : ∀ g x, f (g • x) = ρ g (f x) + c g)
    {b : Fin m → X} (hb : b ∈ torsionSeparated f N) :
    ∃ F : Set (Fin m → X), IsCompact F ∧ invariant G F ∧
      b ∈ F ∧ F ⊆ configuration m X :=
  ⟨torsionSeparated f N, isCompact_torsionSeparated hf hT,
    invariant_torsionSeparated f N ρ c hequiv, hb,
    torsionSeparated_subset_configuration f N⟩

end AffineAction

/-- The standard two-dimensional real torus, coordinatewise modulo one. -/
abbrev StandardTorus := Fin 2 → AddCircle (1 : ℝ)

theorem finite_torsion_standardTorus {N : ℕ} (hN : 0 < N) :
    (torsionPoints N StandardTorus).Finite := by
  have h : {t : AddCircle (1 : ℝ) | N • t = 0}.Finite :=
    AddCircle.finite_torsion 1 hN
  have hpi : (Set.pi (univ : Set (Fin 2))
      (fun _ => {t : AddCircle (1 : ℝ) | N • t = 0})).Finite :=
    Set.Finite.pi (fun _ => h)
  apply hpi.subset
  intro t ht i _
  exact congrFun ht i

end VeechDichotomy
