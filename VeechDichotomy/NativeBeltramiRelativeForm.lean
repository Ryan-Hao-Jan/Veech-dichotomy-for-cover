module

public import VeechDichotomy.NativeBeltramiFibers

/-! Actual relative holomorphic differential coefficients for the
unit-disk family. They satisfy the vertical cocycle law and recover the
nonzero native fiber forms. No global total-space one-form is asserted;
the primitive periods vary with the parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiRelativeForm

open MNEC.NativeAbelianDifferential BeltramiPlane NativeBeltramiSurface NativeBeltramiCharts
open Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

def coefficient (i : X) (p : ℂ × ℂ) : ℂ :=
  ((powerAt q i).exponent : ℂ) * p.2 ^ ((powerAt q i).exponent - 1)

theorem coefficient_holomorphic (i : X) : ContDiff ℂ ω (coefficient q i) :=
  contDiff_const.mul (contDiff_snd.pow _)

theorem fiber_coefficient (μ : Parameter) (i y : Surface q μ)
    (hy : y ∈ (NativeBeltramiSurface.chart q μ i).source) :
    Jacobians.Montel.localRep (NativeBeltramiDifferential.form q μ).val i y =
      coefficient q i.point (NativeBeltramiCharts.chart q i.point (μ, y.point)) :=
  NativeBeltramiDifferential.localRep_eq q μ i y hy

theorem vertical_cocycle (μ : Parameter) (i j : Surface q μ) (z : ℂ)
    (hz : z ∈ ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)).source) :
    coefficient q i.point (μ.val, z) =
      coefficient q j.point (μ.val, ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)) z) *
        fderiv ℂ ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)) z 1 :=
  NativeBeltramiDifferential.coefficient_cocycle q μ i j z hz

theorem continuousOn_product (i : X) :
    ContinuousOn (fun p : Parameter × X => coefficient q i (NativeBeltramiCharts.chart q i p))
      (NativeBeltramiCharts.chart q i).source :=
  (coefficient_holomorphic q i).continuous.comp_continuousOn (NativeBeltramiCharts.chart q i).continuousOn

theorem coefficient_tendsto {J : Type*} {l : Filter J} (i : X) {p : Parameter × X}
    (hp : p ∈ (NativeBeltramiCharts.chart q i).source) {f : J → Parameter × X}
    (hf : Filter.Tendsto f l (𝓝 p)) :
    Filter.Tendsto (fun j => coefficient q i (NativeBeltramiCharts.chart q i (f j))) l
      (𝓝 (coefficient q i (NativeBeltramiCharts.chart q i p))) :=
  ((coefficient_holomorphic q i).continuous.continuousAt.comp
    ((NativeBeltramiCharts.chart q i).continuousAt hp)).tendsto.comp hf

end VeechDichotomy.NativeBeltramiRelativeForm
