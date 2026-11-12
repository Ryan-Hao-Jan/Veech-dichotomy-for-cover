module

public import VeechDichotomy.PhysicalDerivativeAffine
public import VeechDichotomy.NativePhysicalDifferentialEquiv
public import VeechDichotomy.NativeAffineGroup
public import MNEC.NativeLocalPrimitives

/-! Genuine arbitrary native primitive functions satisfy affine germs
under an actual native affine automorphism, on the regular locus.
Comparisons with the constructed native preferred primitives derive the
formula from actual cotangent derivatives and physical affine germs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffinePrimitiveGerms

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveTransitions NativeVeech LinearGroup Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {A : SL2} (φ : AffineAutomorphism q A)

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid := has_translation_groupoid q
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := isManifold q ∞

theorem regular_germ (P Q : X → ℂ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) P y (q.val.toFun y))
    (hQ : ∀ y ∈ V, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) Q y (q.val.toFun y))
    (x : Regular q) (hx : x.val ∈ U) (hfx : (φ.regular x).val ∈ V) :
    ∀ᶠ y in 𝓝 x, toPlane (Q (φ.regular y).val) - linear A (toPlane (P y.val)) =
      toPlane (Q (φ.regular x).val) - linear A (toPlane (P x.val)) := by
  let C := coordinateChart q x
  let D := coordinateChart q (φ.regular x)
  let p := primitiveChart q x
  let r := primitiveChart q (φ.regular x)
  have hPg := MNEC.NativeLocalPrimitives.difference_germ q p P p.source U p.open_source hU
    (chosen q x).derivative hP x.val ⟨(chosen q x).center, hx⟩
  have hQg := MNEC.NativeLocalPrimitives.difference_germ q r Q r.source V r.open_source hV
    (chosen q (φ.regular x)).derivative hQ (φ.regular x).val ⟨(chosen q (φ.regular x)).center, hfx⟩
  have hPnear := (continuous_subtype_val : Continuous (Subtype.val : Regular q → X)).continuousAt hPg
  have hQnear := (continuous_subtype_val.comp φ.regular.continuous).continuousAt hQg
  have hAffine := PhysicalDerivativeAffine.map_affine_germ φ.regular φ.regular.continuous (linear A) φ.derivative
    C D (show C ∈ atlas Plane (Regular q) from ⟨x, rfl⟩)
    (show D ∈ atlas Plane (Regular q) from ⟨φ.regular x, rfl⟩) x
    (coordinateChart_center q x) (coordinateChart_center q (φ.regular x))
  have hPself := hPg.self_of_nhds
  have hQself := hQg.self_of_nhds
  filter_upwards [hPnear, hQnear, hAffine] with y hyP hyQ hyAffine
  have hPplane := congrArg toPlane hyP
  have hQplane := congrArg toPlane hyQ
  have hPplane0 := congrArg toPlane hPself
  have hQplane0 := congrArg toPlane hQself
  simp only [map_add] at hPplane hQplane hPplane0 hQplane0
  change toPlane (P y.val) = C y + toPlane (P x.val - p x.val) at hPplane
  change toPlane (Q (φ.regular y).val) = D (φ.regular y) + toPlane (Q (φ.regular x).val - r (φ.regular x).val) at hQplane
  change toPlane (P x.val) = C x + toPlane (P x.val - p x.val) at hPplane0
  change toPlane (Q (φ.regular x).val) = D (φ.regular x) + toPlane (Q (φ.regular x).val - r (φ.regular x).val) at hQplane0
  rw [hPplane, hQplane, hPplane0, hQplane0, hyAffine, map_add, map_add]
  abel

theorem whole_regular_germ (P Q : X → ℂ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) P y (q.val.toFun y))
    (hQ : ∀ y ∈ V, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) Q y (q.val.toFun y))
    (x : Regular q) (hx : x.val ∈ U) (hfx : φ.surface x.val ∈ V) :
    ∀ᶠ y in 𝓝 x.val, toPlane (Q (φ.surface y)) - linear A (toPlane (P y)) =
      toPlane (Q (φ.surface x.val)) - linear A (toPlane (P x.val)) := by
  apply NativePhysicalDifferentialEquiv.eventually_whole x
    (fun y => toPlane (Q (φ.surface y)) - linear A (toPlane (P y)) =
      toPlane (Q (φ.surface x.val)) - linear A (toPlane (P x.val)))
  have hg := regular_germ q φ P Q U V hU hV hP hQ x hx (by simpa only [φ.value] using hfx)
  simpa only [φ.value] using hg

end VeechDichotomy.NativeAffinePrimitiveGerms
