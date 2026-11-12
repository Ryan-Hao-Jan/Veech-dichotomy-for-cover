module

public import VeechDichotomy.NativePhysicalDifferentialEquiv
public import VeechDichotomy.NativeDeformationRegular
public import VeechDichotomy.NativeAffineGroup

/-! The paper's normalized representatives are related by actual native
holomorphic differential equivalences. Their whole maps are the specified
affine automorphisms conjugated by the constructed deformation maps. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffineNormalization

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open LinearGroup LinearEquivalences NativeVeech NativeDeformationRegular WholeDeformedAtlas
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)

def surfaceMap {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2) :
    WholeSurface q (H * γ) ≃ₜ WholeSurface q H :=
  ((toOriginal q (H * γ)).trans φ.surface).trans (toOriginal q H).symm

def regularMap {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2) :
    Regular (transformed q (H * γ)) ≃ₜ Regular (transformed q H) :=
  (((regularHomeomorph q (H * γ)).symm).trans φ.regular).trans (regularHomeomorph q H)

theorem regularMap_value {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2)
    (x : Regular (transformed q (H * γ))) :
    (regularMap q φ H x).val = surfaceMap q φ H x.val := by
  change (toOriginal q H).symm (φ.regular ((regularHomeomorph q (H * γ)).symm x)).val = _
  rw [φ.value]
  rfl

theorem regularMap_derivative {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2)
    (x : Regular (transformed q (H * γ))) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularMap q φ H) x
      (ContinuousLinearMap.id ℝ Plane) := by
  have hA := hasMFDerivAt_regularHomeomorph_symm q (H * γ) x
  have hφ := φ.derivative ((regularHomeomorph q (H * γ)).symm x)
  have hH := hasMFDerivAt_regularHomeomorph q H
    (φ.regular ((regularHomeomorph q (H * γ)).symm x))
  have hcomp := hH.comp x (hφ.comp x hA)
  have hlin : (planeEquiv H).toContinuousLinearMap.comp
      ((linear γ).comp (planeEquiv (H * γ)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear H).comp ((linear γ).comp (linear (H * γ)⁻¹)) = _
    rw [← ContinuousLinearMap.comp_assoc, ← linear_mul, ← linear_mul, mul_inv_cancel, linear_one]
  rw [hlin] at hcomp
  exact hcomp

theorem regularMap_inverse_derivative {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2)
    (x : Regular (transformed q H)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularMap q φ H).symm x
      (ContinuousLinearMap.id ℝ Plane) := by
  have hH := hasMFDerivAt_regularHomeomorph_symm q H x
  have hφ := φ.inverse_derivative ((regularHomeomorph q H).symm x)
  have hA := hasMFDerivAt_regularHomeomorph q (H * γ)
    (φ.regular.symm ((regularHomeomorph q H).symm x))
  have hcomp := hA.comp x (hφ.comp x hH)
  have hlin : (planeEquiv (H * γ)).toContinuousLinearMap.comp
      ((linear γ⁻¹).comp (planeEquiv H).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ Plane := by
    change (linear (H * γ)).comp ((linear γ⁻¹).comp (linear H⁻¹)) = _
    rw [← ContinuousLinearMap.comp_assoc, ← linear_mul, ← linear_mul]
    simp only [mul_assoc, mul_one, mul_inv_cancel, linear_one]
  rw [hlin] at hcomp
  exact hcomp

def equivalence {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2) :
    MNEC.NativeDifferentialEquiv.Equiv (transformed q (H * γ)) (transformed q H) :=
  NativePhysicalDifferentialEquiv.of_physical_derivatives
    (surfaceMap q φ H) (regularMap q φ H) (regularMap_value q φ H)
    (regularMap_derivative q φ H) (regularMap_inverse_derivative q φ H)

@[simp] theorem equivalence_value {γ : SL2} (φ : AffineAutomorphism q γ) (H : SL2)
    (x : X) :
    (equivalence q φ H).homeomorph ((toOriginal q (H * γ)).symm x) =
      (toOriginal q H).symm (φ.surface x) := rfl

theorem equivalence_normalized_mark {γ : SL2} (φ : AffineAutomorphism q γ)
    (H : SL2) (b : X) :
    (equivalence q φ H).homeomorph ((toOriginal q (H * γ)).symm (φ.surface.symm b)) =
      (toOriginal q H).symm b := by
  rw [equivalence_value, Homeomorph.apply_symm_apply]

end VeechDichotomy.NativeAffineNormalization
