module

public import VeechDichotomy.NativeShearClockGerms
public import VeechDichotomy.NativeAffineClockRigidity

/-! A nontrivial actual native lower-shear affine automorphism with an
actual regular fixed point rules out EVERY dense complete vertical orbit.
Its proved varying local native clock contradicts the proved dense-flow
centralizer rigidity. No cylinder or interval-exchange decomposition is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearFixedPointObstruction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeDirectionalDynamics
open NativeVeech NativePrimitiveRectangles NativeShearMatrices Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem not_dense {a : ℝ} (ha : a ≠ 0) (φ : AffineAutomorphism q (lower a))
    (p : Regular q) (hfix : φ.regular p = p) (x : CompleteOrbits q vertical) :
    ¬ DenseRange (fun t : ℝ => (flow q vertical t x).val.val) := by
  obtain ⟨U, hUgerm, hU, hpU⟩ := mem_nhds_iff.mp (NativeShearClockGerms.local_clock q φ p hfix)
  let V := U ∩ (coordinateChart q p).source
  have hV : IsOpen V := hU.inter (coordinateChart q p).open_source
  have hpV : p ∈ V := ⟨hpU, coordinateChart_center q p⟩
  have hτ : ContinuousOn (NativeShearClockGerms.clock q p a) V :=
    (NativeShearClockGerms.clock_continuousOn q p a).mono inter_subset_right
  have hlocal : ∀ y : CompleteOrbits q vertical, y.val ∈ V →
      φ.regular y.val = trajectory q vertical y.val (NativeShearClockGerms.clock q p a y.val) :=
    fun y hy => hUgerm hy.1
  obtain ⟨y, hy, hyne⟩ := NativeShearClockGerms.clock_nearby_nonzero q p ha V hV hpV
  apply NativeAffineClockRigidity.not_dense_of_nonconstant_clock q φ vertical
    NativeVerticalRayNormalization.vertical_ne_zero (fixes_vertical a) V hV _ hτ hlocal _ x
  exact ⟨y, hy, p, hpV, by simpa only [NativeShearClockGerms.clock_self] using hyne⟩

end VeechDichotomy.NativeShearFixedPointObstruction
