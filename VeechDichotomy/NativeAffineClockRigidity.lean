module

public import VeechDichotomy.NativeAffineDirectionalFlow
public import VeechDichotomy.NativeDenseOrbitInjectivity
public import VeechDichotomy.FlowLocalClockRigidity

/-! A direction-preserving actual affine automorphism on a native
surface with a dense complete orbit has CONSTANT local time displacement.
The flow conjugacy and injectivity hypotheses are proved for the actual
native maps; no global minimality of other orbits is needed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffineClockRigidity

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeVeech LinearGroup LinearEquivalences Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {A : SL2} (φ : AffineAutomorphism q A) (v : Plane)

theorem constant_on_open (hv : v ≠ 0) (hAv : planeEquiv A v = v) (x : CompleteOrbits q v)
    (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val))
    (U : Set (Regular q)) (hU : IsOpen U) (hne : U.Nonempty) (τ : Regular q → ℝ) (hτ : ContinuousOn τ U)
    (hlocal : ∀ y : CompleteOrbits q v, y.val ∈ U → φ.regular y.val = trajectory q v y.val (τ y.val)) :
    ∃ c : ℝ, ∀ y ∈ U, τ y = c := by
  apply FlowLocalClockRigidity.constant_on_open (flow q v) (Subtype.val : CompleteOrbits q v → Regular q)
    (NativeAffineDirectionalFlow.completeMap q φ v hAv) (NativeAffineDirectionalFlow.commutes q φ v hAv) x
    (NativeDenseOrbitInjectivity.flow_injective q v hv x hdense) (NativeDenseOrbitInjectivity.regular_dense q v x hdense)
    U hU hne τ hτ
  intro y hy
  apply Subtype.ext
  exact hlocal y hy

theorem not_dense_of_nonconstant_clock (hv : v ≠ 0) (hAv : planeEquiv A v = v)
    (U : Set (Regular q)) (hU : IsOpen U) (τ : Regular q → ℝ) (hτ : ContinuousOn τ U)
    (hlocal : ∀ y : CompleteOrbits q v, y.val ∈ U → φ.regular y.val = trajectory q v y.val (τ y.val))
    (hnonconstant : ∃ y ∈ U, ∃ z ∈ U, τ y ≠ τ z) (x : CompleteOrbits q v) :
    ¬ DenseRange (fun t : ℝ => (flow q v t x).val.val) := by
  intro hdense
  obtain ⟨y, hy, z, hz, hyz⟩ := hnonconstant
  obtain ⟨c, hc⟩ := constant_on_open q φ v hv hAv x hdense U hU ⟨y, hy⟩ τ hτ hlocal
  exact hyz ((hc y hy).trans (hc z hz).symm)

end VeechDichotomy.NativeAffineClockRigidity
