module

public import MNEC.NativePrimitiveJacobian
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Genuine q-primitive charts have holomorphic inverses. Their actual
intrinsic derivative is nonzero on the regular source; ordinary complex
inverse differentiation in an ORIGINAL curve chart supplies the native
inverse differentiability. No inverse-chart certificate is assumed. -/

@[expose] public section
noncomputable section

namespace MNEC.NativePrimitiveInverse

open NativeAbelianDifferential NativePrimitiveTransitions NativeRegularTranslationAtlas
open Set Filter Topology
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem symm_mdifferentiableAt (q : Differential X) (i : Regular q) (e : PrimitiveChart q i)
    (z : ℂ) (hz : z ∈ e.chart.target) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.chart.symm z := by
  let x := e.chart.symm z
  let c := chartAt ℂ x
  let F := c.symm.trans e.chart
  have hxE : x ∈ e.chart.source := e.chart.map_target hz
  have hxC : x ∈ c.source := mem_chart_source ℂ x
  have ha : c x ∈ c.target := c.map_source hxC
  have hzF : z ∈ F.target := ⟨hz, hxC⟩
  have hcenter : F.symm z = c x := rfl
  have hD := NativePrimitiveJacobian.original_complex_derivative q x ⟨i, e⟩ (c x) ha
    (by rw [c.left_inv hxC]; exact hxE)
  have hne : Jacobians.NativeCanonical.coeffAt q.val x (c x) ≠ 0 := by
    rw [Jacobians.NativeCanonical.coeffAt_self_eq_localRep]
    intro hzero
    exact (e.regular_source hxE) ((toFun_eq_zero_iff_localRep_self q x).mpr hzero)
  have hscalar : HasDerivAt F (Jacobians.NativeCanonical.coeffAt q.val x (c x)) (F.symm z) := by
    rw [hcenter]
    change HasDerivAt (fun w : ℂ => e.chart (c.symm w))
      (Jacobians.NativeCanonical.coeffAt q.val x (c x)) (c x)
    simpa only [c, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      using hD.hasDerivAt
  have hinverse := F.hasDerivAt_symm hzF hne hscalar
  have hcInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (F.symm z) := by
    rw [hcenter]
    exact mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) ha
  have hcomp := hcInv.comp z hinverse.differentiableAt.mdifferentiableAt
  have hnear : ∀ᶠ w in 𝓝 z, e.chart.symm w ∈ c.source :=
    (e.chart.symm.continuousAt hz).eventually (c.open_source.mem_nhds hxC)
  have hfactor : (e.chart.symm : ℂ → X) =ᶠ[𝓝 z] c.symm ∘ F.symm := by
    filter_upwards [hnear] with w hw
    change e.chart.symm w = c.symm (c (e.chart.symm w))
    exact (c.left_inv hw).symm
  exact hcomp.congr_of_eventuallyEq hfactor

theorem mdifferentiable (q : Differential X) (i : Regular q) (e : PrimitiveChart q i) :
    e.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · intro x hx
    exact (e.derivative x hx).mdifferentiableAt.mdifferentiableWithinAt
  · intro z hz
    exact (symm_mdifferentiableAt q i e z hz).mdifferentiableWithinAt

end MNEC.NativePrimitiveInverse

