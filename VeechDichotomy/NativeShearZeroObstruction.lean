module

public import VeechDichotomy.NativeShearFixedPointPeriodicity
public import VeechDichotomy.NativeShearPeriodicPointObstruction
public import VeechDichotomy.NativeAffineZeroPermutation
public import VeechDichotomy.NativeGenusZeros

/-! Any actual nonzero lower-shear derivative on a native surface with
a zero excludes every dense complete vertical orbit. A positive affine
power fixes a genuine zero, the local power fiber supplies a genuine
regular periodic point, and commuting-flow rigidity gives the obstruction.
For genus at least two, existence of the zero is proved intrinsically. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearZeroObstruction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeVeech NativeShearMatrices NativePrimitiveRectangles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem not_dense_of_fixed_point {a : ℝ} (ha : a ≠ 0) (φ : AffineAutomorphism q (lower a))
    (b : X) (hfix : φ.surface b = b) (x : CompleteOrbits q vertical) :
    ¬ DenseRange (fun t : ℝ => (flow q vertical t x).val.val) := by
  obtain ⟨p, n, hn, hperiod⟩ := NativeShearFixedPointPeriodicity.exists_regular_periodic q φ b hfix
  exact NativeShearPeriodicPointObstruction.not_dense q ha φ p hn hperiod x

theorem not_dense_of_zero {a : ℝ} (ha : a ≠ 0) (φ : AffineAutomorphism q (lower a))
    (b : X) (hb : b ∈ zeroSet q) (x : CompleteOrbits q vertical) :
    ¬ DenseRange (fun t : ℝ => (flow q vertical t x).val.val) := by
  obtain ⟨n, hn, hperiod⟩ := NativeAffineZeroPermutation.zero_periodic q φ b hb
  let ψ := NativeAffinePowers.cast q (power a n) (NativeAffinePowers.power q φ n)
  have hfix : ψ.surface b = b := by
    dsimp only [ψ]
    rw [NativeAffinePowers.cast_surface, NativeAffinePowers.power_surface_value]
    exact hperiod
  exact not_dense_of_fixed_point q (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') ha) ψ b hfix x

theorem not_dense (hgenus : 2 ≤ genus X) {a : ℝ} (ha : a ≠ 0)
    (φ : AffineAutomorphism q (lower a)) (x : CompleteOrbits q vertical) :
    ¬ DenseRange (fun t : ℝ => (flow q vertical t x).val.val) := by
  obtain ⟨b, hb⟩ := NativeGenusZeros.zeroSet_nonempty q hgenus
  exact not_dense_of_zero q ha φ b hb x

theorem shear_not_mem_of_dense (hgenus : 2 ≤ genus X) (x : CompleteOrbits q vertical)
    (hdense : DenseRange (fun t : ℝ => (flow q vertical t x).val.val))
    {a : ℝ} (ha : a ≠ 0) : lower a ∉ derivativeGroup q := by
  rintro ⟨φ⟩
  exact not_dense q hgenus ha φ x hdense

end VeechDichotomy.NativeShearZeroObstruction
