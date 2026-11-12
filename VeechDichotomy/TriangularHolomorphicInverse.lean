module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! An actual local homeomorphism of complex bidisks preserving the
first coordinate has an analytic inverse when its vertical derivative
is nonzero. Invertibility of the full derivative is proved here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.TriangularHolomorphicInverse

open Set Filter Topology
open scoped ContDiff

theorem linear_injective (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    (hfirst : ∀ z, (L z).1 = z.1) (hvertical : (L (0, 1)).2 ≠ 0) : Function.Injective L := by
  intro u v huv
  have hz : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hfst : (u - v).1 = 0 := (hfirst (u - v)).symm.trans (congrArg Prod.fst hz)
  have hu : u.1 = v.1 := sub_eq_zero.mp hfst
  have hsplit : u - v = (u.2 - v.2) • ((0, 1) : ℂ × ℂ) := by
    apply Prod.ext
    · change u.1 - v.1 = (u.2 - v.2) * 0
      rw [hu, sub_self, mul_zero]
    · change u.2 - v.2 = (u.2 - v.2) * 1
      rw [mul_one]
  have hs := congrArg Prod.snd hz
  rw [hsplit, map_smul] at hs
  change (u.2 - v.2) * (L (0, 1)).2 = 0 at hs
  exact Prod.ext hu (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hvertical))

theorem linear_equiv (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    (hfirst : ∀ z, (L z).1 = z.1) (hvertical : (L (0, 1)).2 ≠ 0) :
    ∃ T : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), (T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = L := by
  have hi := linear_injective L hfirst hvertical
  let T := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  refine ⟨T, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rfl

theorem contDiffAt_symm (e : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ)) {p : ℂ × ℂ}
    (hp : p ∈ e.source) (he : ContDiffAt ℂ ω e p)
    (hfirst : ∀ᶠ z in 𝓝 p, (e z).1 = z.1)
    (hvertical : (fderiv ℂ e p (0, 1)).2 ≠ 0) : ContDiffAt ℂ ω e.symm (e p) := by
  have hd := (he.differentiableAt (by decide)).hasFDerivAt
  have hfst := hasFDerivAt_fst.comp p hd
  have hEq : (fun z : ℂ × ℂ => (e z).1) =ᶠ[𝓝 p] fun z => z.1 := hfirst
  have hder : (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (fderiv ℂ e p) = ContinuousLinearMap.fst ℂ ℂ ℂ :=
    (hfst.congr_of_eventuallyEq hEq.symm).unique hasFDerivAt_fst
  have hL : ∀ z, (fderiv ℂ e p z).1 = z.1 := fun z => congrArg (fun T : (ℂ × ℂ) →L[ℂ] ℂ => T z) hder
  obtain ⟨T, hT⟩ := linear_equiv (fderiv ℂ e p) hL hvertical
  apply e.contDiffAt_symm (f₀' := T) (e.map_source hp)
  · rw [e.left_inv hp, hT]
    exact hd
  · rw [e.left_inv hp]
    exact he

end VeechDichotomy.TriangularHolomorphicInverse
