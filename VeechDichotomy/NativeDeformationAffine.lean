module

public import VeechDichotomy.NativeDeformationRegular
public import VeechDichotomy.NativeAffinePowers

/-! Conjugating an actual native affine automorphism by the genuine
constructed SL2 deformation produces the computed conjugate derivative.
Whole and regular maps, derivatives and inverse derivatives are explicit. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationAffine

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : ChartedSpace Plane (Regular (transformed q A)) := chartedSpace (transformed q A)

def conjugate {B : SL2} (φ : AffineAutomorphism q B) :
    AffineAutomorphism (transformed q A) (A * B * A⁻¹) where
  surface := ((toOriginal q A).trans φ.surface).trans (toOriginal q A).symm
  regular := (((regularHomeomorph q A).symm).trans φ.regular).trans (regularHomeomorph q A)
  value x := by
    change (regularHomeomorph q A (φ.regular ((regularHomeomorph q A).symm x))).val =
      (toOriginal q A).symm (φ.surface (toOriginal q A x.val))
    rw [regularHomeomorph_value, φ.value]
    rfl
  derivative x := by
    have hi : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A).symm x (linear A⁻¹) := by
      simpa only [planeEquiv_symm] using! hasMFDerivAt_regularHomeomorph_symm q A x
    have ho : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A)
        (φ.regular ((regularHomeomorph q A).symm x)) (linear A) :=
      hasMFDerivAt_regularHomeomorph q A _
    have h := ho.comp x ((φ.derivative ((regularHomeomorph q A).symm x)).comp x hi)
    simpa only [linear_mul, ContinuousLinearMap.comp_assoc] using! h
  inverse_derivative x := by
    have hi : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A).symm x (linear A⁻¹) := by
      simpa only [planeEquiv_symm] using! hasMFDerivAt_regularHomeomorph_symm q A x
    have ho : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A)
        (φ.regular.symm ((regularHomeomorph q A).symm x)) (linear A) :=
      hasMFDerivAt_regularHomeomorph q A _
    have h := ho.comp x ((φ.inverse_derivative ((regularHomeomorph q A).symm x)).comp x hi)
    simpa only [mul_inv_rev, inv_inv, linear_mul, ContinuousLinearMap.comp_assoc] using! h

theorem mem_conjugate_derivative {B : SL2} (hB : B ∈ derivativeGroup q) :
    A * B * A⁻¹ ∈ derivativeGroup (transformed q A) := by
  obtain ⟨φ⟩ := hB
  exact ⟨conjugate q A φ⟩

end VeechDichotomy.NativeDeformationAffine
