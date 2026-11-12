module

public import VeechDichotomy.NativeDeformationActionLaws
public import VeechDichotomy.NativeVerticalRayNormalization

/-! An arbitrary native contracting ray is the unit-vertical ray of
its actual time-zero rotated differential. The matrix identity and
genuine native differential equivalence follow from the proved SL2
deformation composition law. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayFactorization

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential
open NativeDeformationRegular WholeDeformedAtlas LinearGroup NativePrimitiveRectangles
open scoped Manifold ContDiff

theorem diagonal_zero : NativeTeichmullerRay.diagonal 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NativeTeichmullerRay.diagonal]

theorem matrix_zero (v : Plane) (hv : v ≠ 0) :
    NativeTeichmullerRay.matrix v hv 0 = NativeTeichmullerRay.rotationToVertical v hv := by
  rw [NativeTeichmullerRay.matrix, diagonal_zero, one_mul]

theorem matrix_factorization (v : Plane) (hv : v ≠ 0) (hV : vertical ≠ (0 : Plane)) (t : ℝ) :
    NativeTeichmullerRay.matrix vertical hV t * NativeTeichmullerRay.matrix v hv 0 =
      NativeTeichmullerRay.matrix v hv t := by
  rw [NativeVerticalRayNormalization.matrix_vertical, matrix_zero]
  rfl

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.chartedSpace (transformed q A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.isComplexManifold (transformed q A) B ω

def matrix_equivalence (A B : SL2) (h : A = B) :
    MNEC.NativeDifferentialEquiv.Equiv (transformed q A) (transformed q B) := by
  subst B
  exact NativeDifferentialEquivalenceLaws.refl (transformed q A)

def equivalence (v : Plane) (hv : v ≠ 0) (hV : vertical ≠ (0 : Plane)) (t : ℝ) :
    MNEC.NativeDifferentialEquiv.Equiv
      (NativeTeichmullerRay.rayForm (NativeTeichmullerRay.rayForm q v hv 0) vertical hV t)
      (NativeTeichmullerRay.rayForm q v hv t) := by
  exact NativeDifferentialEquivalenceLaws.trans
    (NativeDeformationActionLaws.composition q
      (NativeTeichmullerRay.matrix v hv 0) (NativeTeichmullerRay.matrix vertical hV t))
    (matrix_equivalence q _ _ (matrix_factorization v hv hV t))

end VeechDichotomy.NativeRayFactorization
