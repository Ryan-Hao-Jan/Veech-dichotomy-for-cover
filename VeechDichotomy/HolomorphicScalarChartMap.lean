module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! A continuous curve map with a genuine nonzero scalar chart formula
is holomorphic. Differentiating that formula gives its intrinsic native
cotangent pullback, without an assumed physical-derivative certificate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicScalarChartMap

open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

theorem inverse_scalar {c s t : ℂ} (hc : c ≠ 0) (h : s = c * t) : t = c⁻¹ * s := by
  rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem mdifferentiableAt (H : M → N) (hH : Continuous H)
    (s : OpenPartialHomeomorph M ℂ) (t : OpenPartialHomeomorph N ℂ)
    (hs : s.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (ht : t.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    {x : M} (hxs : x ∈ s.source) (hxt : H x ∈ t.source) {c : ℂ} (hc : c ≠ 0)
    (hformula : ∀ᶠ y in 𝓝 x, s y = c * t (H y)) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H x := by
  have hvalue : c⁻¹ * s x = t (H x) := (inverse_scalar hc hformula.self_of_nhds).symm
  have harg : c⁻¹ * s x ∈ t.target := hvalue ▸ t.map_source hxt
  have hmul : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => c⁻¹ * z) (s x) :=
    (hasDerivAt_const_mul c⁻¹).differentiableAt.mdifferentiableAt
  apply ((ht.mdifferentiableAt_symm harg).comp x (hmul.comp x (hs.mdifferentiableAt hxs))).congr_of_eventuallyEq
  filter_upwards [hformula, hH.continuousAt (t.open_source.mem_nhds hxt)] with y hy hyt
  change H y = t.symm (c⁻¹ * s y)
  rw [← inverse_scalar hc hy, t.left_inv hyt]

theorem derivative_relation (H : M → N) (s : M → ℂ) (t : N → ℂ) {x : M} {c : ℂ}
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H x) (ht : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t (H x))
    (hformula : ∀ᶠ y in 𝓝 x, s y = c * t (H y)) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) s x = (c • mfderiv 𝓘(ℂ) 𝓘(ℂ) t (H x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H x) := by
  have hmul : HasFDerivAt (fun z : ℂ => c * z) (c • ContinuousLinearMap.id ℂ ℂ) (t (H x)) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      (hasDerivAt_const_mul c : HasDerivAt (fun z : ℂ => c * z) c (t (H x)))
  have hcomp := hmul.hasMFDerivAt.comp x (ht.hasMFDerivAt.comp x hH.hasMFDerivAt)
  have hs := hcomp.congr_of_eventuallyEq_abuse hformula
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using! hs.mfderiv

end VeechDichotomy.HolomorphicScalarChartMap
