module

public import VeechDichotomy.NativeSurface
public import VeechDichotomy.LinearGroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.MeasureTheory.Group.Action

/-! Adapted from the supplied October 30 NativeVeech.lean. Only the small
SL2 matrix action is used, avoiding the unrelated slit-surface imports.

The Veech condition is defined independently of any splitting,
coefficient or orbit-density conclusion. The derivative subgroup consists
of actual whole-curve homeomorphisms whose regular restrictions are native
real affine maps with the displayed constant determinant-one derivative.
A lattice means a discrete subgroup with finite nonzero invariant volume
on its actual homogeneous quotient (normalized here to probability). -/

@[expose] public section
noncomputable section
namespace VeechDichotomy.NativeVeech

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open LinearGroup MeasureTheory Set
open scoped Manifold ContDiff

set_option autoImplicit false

def linear (A : SL2) : Plane →L[ℝ] Plane :=
  ({ toFun := act A
     map_add' := by intro p q; ext <;> simp [act] <;> ring
     map_smul' := by intro a p; ext <;> simp [act] <;> ring } : Plane →ₗ[ℝ] Plane).toContinuousLinearMap

@[simp] theorem linear_apply (A : SL2) (p : Plane) : linear A p = act A p := rfl

theorem linear_one : linear (1 : SL2) = ContinuousLinearMap.id ℝ Plane := by
  apply ContinuousLinearMap.ext
  intro p
  ext <;> simp [linear, act, Matrix.SpecialLinearGroup.coe_one]

theorem linear_mul (A B : SL2) : linear (A * B) = (linear A).comp (linear B) := by
  apply ContinuousLinearMap.ext
  intro p
  ext <;> simp [linear, act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] <;> ring

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)
local instance : ChartedSpace Plane (Regular q) := chartedSpace q

structure AffineAutomorphism (A : SL2) where
  surface : X ≃ₜ X
  regular : Regular q ≃ₜ Regular q
  value : ∀ x : Regular q, (regular x).val = surface x.val
  derivative : ∀ x : Regular q,
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) regular x (linear A)
  inverse_derivative : ∀ x : Regular q,
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) regular.symm x (linear A⁻¹)

namespace AffineAutomorphism

def identity : AffineAutomorphism q (1 : SL2) where
  surface := Homeomorph.refl X
  regular := Homeomorph.refl (Regular q)
  value _ := rfl
  derivative x := by rw [linear_one]; exact hasMFDerivAt_id x
  inverse_derivative x := by rw [inv_one, linear_one]; exact hasMFDerivAt_id x

def multiply {A B : SL2} (e : AffineAutomorphism q A) (f : AffineAutomorphism q B) :
    AffineAutomorphism q (A * B) where
  surface := f.surface.trans e.surface
  regular := f.regular.trans e.regular
  value x := by change (e.regular (f.regular x)).val = e.surface (f.surface x.val); rw [e.value, f.value]
  derivative x := by
    rw [linear_mul]
    exact (e.derivative (f.regular x)).comp x (f.derivative x)
  inverse_derivative x := by
    rw [mul_inv_rev, linear_mul]
    exact (f.inverse_derivative (e.regular.symm x)).comp x (e.inverse_derivative x)

def inverse {A : SL2} (e : AffineAutomorphism q A) : AffineAutomorphism q A⁻¹ where
  surface := e.surface.symm
  regular := e.regular.symm
  value x := by
    apply e.surface.injective
    rw [Homeomorph.apply_symm_apply, ← e.value, Homeomorph.apply_symm_apply]
  derivative := e.inverse_derivative
  inverse_derivative x := by rw [inv_inv]; exact e.derivative x

end AffineAutomorphism

def derivativeGroup : Subgroup SL2 where
  carrier := {A | Nonempty (AffineAutomorphism q A)}
  one_mem' := ⟨AffineAutomorphism.identity q⟩
  mul_mem' := by rintro A B ⟨e⟩ ⟨f⟩; exact ⟨AffineAutomorphism.multiply q e f⟩
  inv_mem' := by rintro A ⟨e⟩; exact ⟨AffineAutomorphism.inverse q e⟩

theorem mem_derivativeGroup_iff (A : SL2) :
    A ∈ derivativeGroup q ↔ Nonempty (AffineAutomorphism q A) := Iff.rfl

instance quotientMeasurableSpace (Γ : Subgroup SL2) : MeasurableSpace (SL2 ⧸ Γ) :=
  borel (SL2 ⧸ Γ)

def IsLattice (Γ : Subgroup SL2) : Prop :=
  DiscreteTopology Γ ∧ ∃ μ : Measure (SL2 ⧸ Γ),
    IsProbabilityMeasure μ ∧ SMulInvariantMeasure SL2 (SL2 ⧸ Γ) μ

def IsVeech : Prop := IsLattice (derivativeGroup q)

end VeechDichotomy.NativeVeech

