module

public import VeechDichotomy.NativeDeformationActionLaws

/-! Actual cancellation of two native SL2 deformations whose matrices
multiply to the identity. The whole-curve homeomorphism literally unwraps
the two surface wrappers, retaining exact underlying-point formulas. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationCancellation

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences NativeVeech
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed q A) B) := WholeDeformedAtlas.chartedSpace (transformed q A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed q A) B) := WholeDeformedAtlas.isComplexManifold (transformed q A) B ω
local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed q A)) := MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)
local instance (A B : SL2) : ChartedSpace Plane (Regular (transformed (transformed q A) B)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed (transformed q A) B)

def sourceHomeomorph (A B : SL2) : WholeSurface (transformed q A) B ≃ₜ X :=
  (toOriginal (transformed q A) B).trans (toOriginal q A)

def regularHomeomorph (A B : SL2) : Regular (transformed (transformed q A) B) ≃ₜ Regular q :=
  (NativeDeformationRegular.regularHomeomorph (transformed q A) B).symm.trans
    (NativeDeformationRegular.regularHomeomorph q A).symm

theorem regular_value (A B : SL2) (x : Regular (transformed (transformed q A) B)) :
    (regularHomeomorph q A B x).val = sourceHomeomorph q A B x.val := rfl

theorem regular_derivative (A B : SL2) (h : B * A = 1)
    (x : Regular (transformed (transformed q A) B)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A B) x (ContinuousLinearMap.id ℝ Plane) := by
  have hB := hasMFDerivAt_regularHomeomorph_symm (transformed q A) B x
  have hA := hasMFDerivAt_regularHomeomorph_symm q A
    ((NativeDeformationRegular.regularHomeomorph (transformed q A) B).symm x)
  have hd := hA.comp x hB
  have hlin : (planeEquiv A).symm.toContinuousLinearMap.comp (planeEquiv B).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear A⁻¹).comp (linear B⁻¹) = _
    rw [← linear_mul, ← mul_inv_rev, h, inv_one, linear_one]
  rw [hlin] at hd
  exact hd

theorem inverse_derivative (A B : SL2) (h : B * A = 1) (x : Regular q) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A B).symm x (ContinuousLinearMap.id ℝ Plane) := by
  have hA := hasMFDerivAt_regularHomeomorph q A x
  have hB := hasMFDerivAt_regularHomeomorph (transformed q A) B
    (NativeDeformationRegular.regularHomeomorph q A x)
  have hd := hB.comp x hA
  have hlin : (planeEquiv B).toContinuousLinearMap.comp (planeEquiv A).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear B).comp (linear A) = _
    rw [← linear_mul, h, linear_one]
  rw [hlin] at hd
  exact hd

def equivalence (A B : SL2) (h : B * A = 1) :
    MNEC.NativeDifferentialEquiv.Equiv (transformed (transformed q A) B) q :=
  NativePhysicalDifferentialEquiv.of_physical_derivatives (sourceHomeomorph q A B)
    (regularHomeomorph q A B) (regular_value q A B) (regular_derivative q A B h) (inverse_derivative q A B h)

theorem equivalence_value (A B : SL2) (h : B * A = 1) (x : WholeSurface (transformed q A) B) :
    (equivalence q A B h).homeomorph x = x.point.point := rfl

end VeechDichotomy.NativeDeformationCancellation
