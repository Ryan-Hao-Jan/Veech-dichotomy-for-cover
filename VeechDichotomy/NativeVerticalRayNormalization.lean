module

public import VeechDichotomy.NativeRayReferenceTimes

/-! Exact normalization of the actual unit-vertical native ray: its
rotation is the identity, its transverse velocity is horizontal and its
reference clock is exp(t). No choice of direction or time is suppressed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeVerticalRayNormalization

open MNEC.LatticeTorus LinearGroup LinearEquivalences NativePrimitiveRectangles

theorem vertical_ne_zero : vertical ≠ (0 : Plane) := by
  intro h
  have h2 := congrArg Prod.snd h
  norm_num [vertical] at h2

theorem radius_vertical : NativeTeichmullerRay.radius vertical = 1 := by
  simp [NativeTeichmullerRay.radius, vertical]

theorem rotation_vertical (hv : vertical ≠ (0 : Plane)) :
    NativeTeichmullerRay.rotationToVertical vertical hv = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NativeTeichmullerRay.rotationToVertical, NativeTeichmullerRay.radius, vertical]

theorem transverse_vertical (hv : vertical ≠ (0 : Plane)) :
    NativeRayRectangleComparison.transverse vertical hv = horizontal := by
  simp [NativeRayRectangleComparison.transverse, rotation_vertical, planeEquiv_one]

theorem matrix_vertical (hv : vertical ≠ (0 : Plane)) (t : ℝ) :
    NativeTeichmullerRay.matrix vertical hv t = NativeTeichmullerRay.diagonal t := by
  rw [NativeTeichmullerRay.matrix, rotation_vertical, mul_one]

theorem contraction_vertical (t : ℝ) : NativeTeichmullerRay.contraction vertical t = Real.exp (-t) := by
  rw [NativeTeichmullerRay.contraction, radius_vertical, mul_one]

theorem reference_vertical (t : ℝ) : NativeRayReferenceTimes.reference vertical t = Real.exp t := by
  rw [NativeRayReferenceTimes.reference, contraction_vertical, Real.exp_neg, inv_inv]

end VeechDichotomy.NativeVerticalRayNormalization
