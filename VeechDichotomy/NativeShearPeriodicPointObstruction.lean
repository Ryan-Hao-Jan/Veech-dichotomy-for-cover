module

public import VeechDichotomy.NativeShearFixedPointObstruction
public import VeechDichotomy.NativeAffinePowers

/-! A nonzero native lower-shear affine automorphism with ANY actual
regular periodic point rules out a dense complete vertical orbit.
The genuine positive affine power fixes that point and has a computed
nonzero shear parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearPeriodicPointObstruction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeVeech NativeShearMatrices NativePrimitiveRectangles
open Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem not_dense {a : ℝ} (ha : a ≠ 0) (φ : AffineAutomorphism q (lower a))
    (p : Regular q) {n : ℕ} (hn : 0 < n) (hperiod : (φ.regular^[n]) p = p)
    (x : CompleteOrbits q vertical) : ¬ DenseRange (fun t : ℝ => (flow q vertical t x).val.val) := by
  let ψ := NativeAffinePowers.cast q (power a n) (NativeAffinePowers.power q φ n)
  have hfix : ψ.regular p = p := by
    dsimp only [ψ]
    rw [NativeAffinePowers.cast_regular, NativeAffinePowers.power_regular_value]
    exact hperiod
  have hparam : (n : ℝ) * a ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') ha
  exact NativeShearFixedPointObstruction.not_dense q hparam ψ p hfix x

end VeechDichotomy.NativeShearPeriodicPointObstruction
