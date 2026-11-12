module

public import VeechDichotomy.NativeAffineNormalization
public import VeechDichotomy.NativeDifferentialEquivalenceLaws

/-! Identity and multiplication for the constructed compact SL2
deformations, up to genuine native differential equivalence. The maps
are the literal identifications of underlying points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationActionLaws

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open LinearGroup LinearEquivalences NativeVeech NativeDeformationRegular WholeDeformedAtlas
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.chartedSpace (transformed q A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.isComplexManifold (transformed q A) B ω
local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)
local instance (A B : SL2) : ChartedSpace Plane (Regular (transformed (transformed q A) B)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed (transformed q A) B)

def identity : MNEC.NativeDifferentialEquiv.Equiv q (transformed q 1) :=
  NativePhysicalDifferentialEquiv.of_physical_derivatives (toOriginal q 1).symm
    (regularHomeomorph q 1) (regularHomeomorph_value q 1)
    (fun x => by simpa only [planeEquiv_one] using! hasMFDerivAt_regularHomeomorph q 1 x)
    (fun y => by simpa only [planeEquiv_one] using! hasMFDerivAt_regularHomeomorph_symm q 1 y)

def compositionSurface (A B : SL2) :
    WholeSurface (transformed q A) B ≃ₜ WholeSurface q (B * A) :=
  ((toOriginal (transformed q A) B).trans (toOriginal q A)).trans (toOriginal q (B * A)).symm

def compositionRegular (A B : SL2) :
    Regular (transformed (transformed q A) B) ≃ₜ Regular (transformed q (B * A)) :=
  (((regularHomeomorph (transformed q A) B).symm).trans (regularHomeomorph q A).symm).trans
    (regularHomeomorph q (B * A))

theorem compositionRegular_value (A B : SL2)
    (x : Regular (transformed (transformed q A) B)) :
    (compositionRegular q A B x).val = compositionSurface q A B x.val := rfl

theorem compositionRegular_derivative (A B : SL2)
    (x : Regular (transformed (transformed q A) B)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (compositionRegular q A B) x
      (ContinuousLinearMap.id ℝ Plane) := by
  have hB := hasMFDerivAt_regularHomeomorph_symm (transformed q A) B x
  have hA := hasMFDerivAt_regularHomeomorph_symm q A
    ((regularHomeomorph (transformed q A) B).symm x)
  have hBA := hasMFDerivAt_regularHomeomorph q (B * A)
    ((regularHomeomorph q A).symm ((regularHomeomorph (transformed q A) B).symm x))
  have hcomp := hBA.comp x (hA.comp x hB)
  have hlin : (planeEquiv (B * A)).toContinuousLinearMap.comp
      ((planeEquiv A).symm.toContinuousLinearMap.comp (planeEquiv B).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear (B * A)).comp ((linear A⁻¹).comp (linear B⁻¹)) = _
    rw [← ContinuousLinearMap.comp_assoc, ← linear_mul, ← linear_mul]
    simp only [mul_assoc, mul_inv_cancel, mul_one, linear_one]
  rw [hlin] at hcomp
  exact hcomp

theorem compositionRegular_inverse_derivative (A B : SL2)
    (x : Regular (transformed q (B * A))) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (compositionRegular q A B).symm x
      (ContinuousLinearMap.id ℝ Plane) := by
  have hBA := hasMFDerivAt_regularHomeomorph_symm q (B * A) x
  have hA := hasMFDerivAt_regularHomeomorph q A ((regularHomeomorph q (B * A)).symm x)
  have hB := hasMFDerivAt_regularHomeomorph (transformed q A) B
    (regularHomeomorph q A ((regularHomeomorph q (B * A)).symm x))
  have hcomp := hB.comp x (hA.comp x hBA)
  have hlin : (planeEquiv B).toContinuousLinearMap.comp
      ((planeEquiv A).toContinuousLinearMap.comp (planeEquiv (B * A)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear B).comp ((linear A).comp (linear (B * A)⁻¹)) = _
    rw [← ContinuousLinearMap.comp_assoc, ← linear_mul, ← linear_mul, mul_inv_cancel, linear_one]
  rw [hlin] at hcomp
  exact hcomp

def composition (A B : SL2) : MNEC.NativeDifferentialEquiv.Equiv
    (transformed (transformed q A) B) (transformed q (B * A)) :=
  NativePhysicalDifferentialEquiv.of_physical_derivatives
    (compositionSurface q A B) (compositionRegular q A B) (compositionRegular_value q A B)
    (compositionRegular_derivative q A B) (compositionRegular_inverse_derivative q A B)

@[simp] theorem composition_value (A B : SL2) (x : X) :
    (composition q A B).homeomorph ((toOriginal (transformed q A) B).symm ((toOriginal q A).symm x)) =
      (toOriginal q (B * A)).symm x := rfl

end VeechDichotomy.NativeDeformationActionLaws
