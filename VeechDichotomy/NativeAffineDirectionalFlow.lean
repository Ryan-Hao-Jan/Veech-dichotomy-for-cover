module

public import VeechDichotomy.NativeDeformationFlow
public import VeechDichotomy.NativeAffineGroup

/-! Actual native affine automorphisms transport directional lifetimes
and trajectories by their actual derivative. If a velocity is fixed,
the induced actual complete-phase map commutes with every flow time. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffineDirectionalFlow

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeVeech LinearGroup LinearEquivalences Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {A : SL2} (φ : AffineAutomorphism q A)

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid := has_translation_groupoid q
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := isManifold q ∞

theorem domain_eq (v : Plane) (x : Regular q) :
    domain q v x = domain q (planeEquiv A v) (φ.regular x) :=
  MNEC.TranslationLinearFlowConjugacy.domain_eq φ.regular (planeEquiv A) φ.derivative
    (fun y => by simpa only [planeEquiv_symm] using! φ.inverse_derivative y) v x

theorem trajectory_conjugacy (v : Plane) (x : Regular q) (t : ℝ) (ht : t ∈ domain q v x) :
    φ.regular (trajectory q v x t) = trajectory q (planeEquiv A v) (φ.regular x) t :=
  MNEC.TranslationLinearFlowConjugacy.trajectory_conjugacy φ.regular (planeEquiv A) φ.derivative v x t ht

theorem complete_forward (v : Plane) (hAv : planeEquiv A v = v) (x : CompleteOrbits q v) :
    φ.regular x.val ∈ completeOrbitSet q v := by
  change domain q v (φ.regular x.val) = univ
  have hD : domain q v x.val = domain q v (φ.regular x.val) := by
    simpa only [hAv] using domain_eq q φ v x.val
  exact hD.symm.trans x.property

def completeMap (v : Plane) (hAv : planeEquiv A v = v) (x : CompleteOrbits q v) : CompleteOrbits q v :=
  ⟨φ.regular x.val, complete_forward q φ v hAv x⟩

theorem completeMap_value (v : Plane) (hAv : planeEquiv A v = v) (x : CompleteOrbits q v) :
    (completeMap q φ v hAv x).val = φ.regular x.val := rfl

theorem commutes (v : Plane) (hAv : planeEquiv A v = v) (t : ℝ) (x : CompleteOrbits q v) :
    completeMap q φ v hAv (flow q v t x) = flow q v t (completeMap q φ v hAv x) := by
  apply Subtype.ext
  change φ.regular (trajectory q v x.val t) = trajectory q v (φ.regular x.val) t
  simpa only [hAv] using trajectory_conjugacy q φ v x.val t (complete_time_mem q v x t)

end VeechDichotomy.NativeAffineDirectionalFlow
