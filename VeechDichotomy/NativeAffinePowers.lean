module

public import VeechDichotomy.NativeAffineGroup

/-! Actual powers of indexed native affine automorphisms. Matrix casts
retain the literal point maps, and each constructed power acts by the
actual iterate on both the regular locus and the whole native surface. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffinePowers

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech LinearGroup
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

def cast {A B : SL2} (h : A = B) (φ : AffineAutomorphism q A) : AffineAutomorphism q B := by
  cases h
  exact φ

theorem cast_regular {A B : SL2} (h : A = B) (φ : AffineAutomorphism q A) (x : Regular q) :
    (cast q h φ).regular x = φ.regular x := by cases h; rfl

theorem cast_surface {A B : SL2} (h : A = B) (φ : AffineAutomorphism q A) (x : X) :
    (cast q h φ).surface x = φ.surface x := by cases h; rfl

def power {A : SL2} (φ : AffineAutomorphism q A) : (n : ℕ) → AffineAutomorphism q (A ^ n)
  | 0 => cast q (pow_zero A).symm (AffineAutomorphism.identity q)
  | n + 1 => cast q (pow_succ A n).symm (AffineAutomorphism.multiply q (power φ n) φ)

theorem power_regular_value {A : SL2} (φ : AffineAutomorphism q A) (n : ℕ) (x : Regular q) :
    (power q φ n).regular x = (φ.regular^[n]) x := by
  induction n generalizing x with
  | zero => rw [power, cast_regular]; rfl
  | succ n ih =>
    rw [power, cast_regular]
    change (power q φ n).regular (φ.regular x) = (φ.regular^[n + 1]) x
    rw [ih, Function.iterate_succ_apply]

theorem power_surface_value {A : SL2} (φ : AffineAutomorphism q A) (n : ℕ) (x : X) :
    (power q φ n).surface x = (φ.surface^[n]) x := by
  induction n generalizing x with
  | zero => rw [power, cast_surface]; rfl
  | succ n ih =>
    rw [power, cast_surface]
    change (power q φ n).surface (φ.surface x) = (φ.surface^[n + 1]) x
    rw [ih, Function.iterate_succ_apply]

end VeechDichotomy.NativeAffinePowers
