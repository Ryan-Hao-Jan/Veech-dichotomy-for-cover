module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
The actual finite configuration spaces used in Theorem 1 of the paper.
No translation-surface or dynamical theorem is assumed here.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

variable {X : Type*} {m : ℕ}

/-- Ordered tuples of pairwise distinct points, as a subset of the full product. -/
def configuration (m : ℕ) (X : Type*) : Set (Fin m → X) :=
  {b | Function.Injective b}

/-- The fat diagonal, including every possible coordinate collision. -/
def fatDiagonal (m : ℕ) (X : Type*) : Set (Fin m → X) :=
  {b | ∃ i j, i ≠ j ∧ b i = b j}

theorem configuration_eq_compl_fatDiagonal :
    configuration m X = (fatDiagonal m X)ᶜ := by
  ext b
  simp only [configuration, fatDiagonal, mem_ofPred_eq, mem_compl_iff]
  constructor
  · rintro h ⟨i, j, hij, heq⟩
    exact hij (h heq)
  · intro h i j heq
    by_contra hij
    exact h ⟨i, j, hij, heq⟩

theorem configuration_zero : configuration 0 X = univ := by
  ext b
  simp only [configuration, mem_ofPred_eq, mem_univ, iff_true]
  exact Function.injective_of_subsingleton b

theorem configuration_one : configuration 1 X = univ := by
  ext b
  simp only [configuration, mem_ofPred_eq, mem_univ, iff_true]
  exact Function.injective_of_subsingleton b

section Topology

variable [TopologicalSpace X] [T2Space X]

theorem isClosed_fatDiagonal : IsClosed (fatDiagonal m X) := by
  have heq : fatDiagonal m X =
      ⋃ i : Fin m, ⋃ j : Fin m, ⋃ (_ : i ≠ j), {b | b i = b j} := by
    ext b
    simp [fatDiagonal]
  rw [heq]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem isOpen_configuration : IsOpen (configuration m X) := by
  rw [configuration_eq_compl_fatDiagonal]
  exact isClosed_fatDiagonal.isOpen_compl

end Topology

/-- Invariance under every element of a group acting on a space. -/
def invariant (G : Type*) {Z : Type*} [SMul G Z] (F : Set Z) : Prop :=
  ∀ (g : G) ⦃z : Z⦄, z ∈ F → g • z ∈ F

section OrbitClosure

variable {G Z : Type*} [Group G] [MulAction G Z]

theorem invariant_orbit (b : Z) : invariant G (MulAction.orbit G b) := by
  intro g z hz
  rcases hz with ⟨k, rfl⟩
  exact ⟨g * k, mul_smul g k b⟩

variable [TopologicalSpace Z] [ContinuousConstSMul G Z]

theorem invariant_closure {F : Set Z} (hF : invariant G F) :
    invariant G (closure F) := by
  intro g z hz
  exact (Set.MapsTo.closure (hF g) (continuous_const_smul g)) hz

variable [T2Space Z] [CompactSpace Z]

/-- The precise orbit-closure reformulation used immediately after Theorem 1. -/
theorem exists_compact_invariant_iff_orbitClosure_subset
    (b : Z) (U : Set Z) :
    (∃ F : Set Z, IsCompact F ∧ invariant G F ∧ b ∈ F ∧ F ⊆ U) ↔
      closure (MulAction.orbit G b) ⊆ U := by
  constructor
  · rintro ⟨F, hFc, hFi, hbF, hFU⟩
    apply Set.Subset.trans _ hFU
    apply closure_minimal _ hFc.isClosed
    rintro z ⟨g, rfl⟩
    exact hFi g hbF
  · intro h
    exact ⟨closure (MulAction.orbit G b), isClosed_closure.isCompact,
      invariant_closure (invariant_orbit b),
      subset_closure (MulAction.mem_orbit_self b), h⟩

end OrbitClosure

section TupleActions

variable {G : Type*} [Group G] [MulAction G X]

theorem invariant_configuration : invariant G (configuration m X) := by
  intro g b hb i j hij
  apply hb
  exact (MulAction.injective g) hij

variable [TopologicalSpace X] [T2Space X] [CompactSpace X] [ContinuousConstSMul G X]

theorem compact_configuration_iff_orbitClosure_avoids_diagonal (b : Fin m → X) :
    (∃ F : Set (Fin m → X), IsCompact F ∧ invariant G F ∧
      b ∈ F ∧ F ⊆ configuration m X) ↔
      Disjoint (closure (MulAction.orbit G b)) (fatDiagonal m X) := by
  rw [exists_compact_invariant_iff_orbitClosure_subset,
    configuration_eq_compl_fatDiagonal]
  simp only [Set.subset_def, mem_compl_iff, Set.disjoint_left]

omit [T2Space X] [ContinuousConstSMul G X] in
/-- Covers with zero or one branch value automatically meet the configuration condition. -/
theorem exists_compact_invariant_configuration_of_subsingleton
    [Subsingleton (Fin m)] (b : Fin m → X) :
    ∃ F : Set (Fin m → X), IsCompact F ∧ invariant G F ∧
      b ∈ F ∧ F ⊆ configuration m X := by
  refine ⟨univ, isCompact_univ, ?_, mem_univ b, ?_⟩
  · intro g z _
    exact mem_univ _
  · intro z _
    exact Function.injective_of_subsingleton z

end TupleActions

end VeechDichotomy
