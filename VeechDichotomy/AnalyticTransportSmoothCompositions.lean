module

public import VeechDichotomy.AnalyticTransportCompositions
public import VeechDichotomy.HolomorphicCurveGerms

/-! The explicit parameter-dependent transport compositions are analytic
in the finite-dimensional complex parameter and curve coordinate. This is
proved by composing analytic one-variable curve germs and continuous-linear
parameter evaluation, without invoking an unproved several-variable upgrade. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.AnalyticTransportSmoothCompositions

open Set Filter Metric Topology LocalTranslationPlane PointTransportDisk
open ComplexDisplacementParameters PointTransportUniform AnalyticTransportCoordinates
open AnalyticTransportCompositions HolomorphicCurveGerms
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable (D : Fin m → Disk (X := X)) (F : (Fin m → Parameter) → X ≃ₜ X)
  (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)

include hown in
theorem forward_contMDiffAt (i : Fin m) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (f : ℂ → X) (p : Space m × ℂ) (ha : p.1 ∈ domain m)
    (hx : f p.2 ∈ innerDisk (D i)) (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f p.2) :
    ContMDiffAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) ω (fun q : Space m × ℂ => ambientTransport F q.1 (f q.2)) p := by
  have hv := ((chart_contMDiffAt (D i).chart hD hx.1).comp p.2 hf).contDiffAt
  have heval : ContDiffAt ℂ ω (fun q : Space m × ℂ => q.1 i) p :=
    ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).contDiff.contDiffAt).comp p contDiffAt_fst
  have hsum := (hv.comp p contDiffAt_snd).add heval
  have ht : (D i).chart (f p.2) + p.1 i ∈ (D i).chart.target :=
    translated_target (D i) ⟨p.1 i, ha i⟩ hx
  apply ((chart_contMDiffAt_symm (D i).chart hD ht).comp p hsum.contMDiffAt).congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ha
  have hinner : ∀ᶠ q : Space m × ℂ in 𝓝 p, f q.2 ∈ innerDisk (D i) :=
    (hf.continuousAt.comp continuous_snd.continuousAt) ((innerDisk_open (D i)).mem_nhds hx)
  filter_upwards [hparam, hinner] with q hq hqi
  exact forward_point_formula D F hown hq i hqi

include hown in
theorem forward_contDiffAt (i : Fin m) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (f : ℂ → X) (g : X → ℂ) (p : Space m × ℂ) (ha : p.1 ∈ domain m)
    (hx : f p.2 ∈ innerDisk (D i)) (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f p.2)
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (ambientTransport F p.1 (f p.2))) :
    ContDiffAt ℂ ω (fun q : Space m × ℂ => g (ambientTransport F q.1 (f q.2))) p := by
  have hv := ((chart_contMDiffAt (D i).chart hD hx.1).comp p.2 hf).contDiffAt
  have heval : ContDiffAt ℂ ω (fun q : Space m × ℂ => q.1 i) p :=
    ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).contDiff.contDiffAt).comp p contDiffAt_fst
  have hsum := (hv.comp p contDiffAt_snd).add heval
  have ht : (D i).chart (f p.2) + p.1 i ∈ (D i).chart.target :=
    translated_target (D i) ⟨p.1 i, ha i⟩ hx
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((D i).chart.symm ((D i).chart (f p.2) + p.1 i)) := by
    rwa [forward_point_formula D F hown ha i hx] at hg
  have hd := (hg'.comp p ((chart_contMDiffAt_symm (D i).chart hD ht).comp p hsum.contMDiffAt)).contDiffAt
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ha
  have hinner : ∀ᶠ q : Space m × ℂ in 𝓝 p, f q.2 ∈ innerDisk (D i) :=
    (hf.continuousAt.comp continuous_snd.continuousAt) ((innerDisk_open (D i)).mem_nhds hx)
  filter_upwards [hparam, hinner] with q hq hqi
  exact congrArg g (forward_point_formula D F hown hq i hqi)

include hown in
theorem inverse_contDiffAt (i : Fin m) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (f : ℂ → X) (g : X → ℂ) (p : Space m × ℂ) (ha : p.1 ∈ domain m)
    (hx : f p.2 ∈ (D i).chart.source) (hn : ‖(D i).chart (f p.2) - p.1 i‖ < 1)
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f p.2)
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((ambientTransport F p.1).symm (f p.2))) :
    ContDiffAt ℂ ω (fun q : Space m × ℂ => g ((ambientTransport F q.1).symm (f q.2))) p := by
  have hv := ((chart_contMDiffAt (D i).chart hD hx).comp p.2 hf).contDiffAt
  have heval : ContDiffAt ℂ ω (fun q : Space m × ℂ => q.1 i) p :=
    ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).contDiff.contDiffAt).comp p contDiffAt_fst
  have hsub := (hv.comp p contDiffAt_snd).sub heval
  have ht : (D i).chart (f p.2) - p.1 i ∈ (D i).chart.target := (D i).closedBall_target (by
    rw [mem_closedBall, dist_zero_right]
    linarith)
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((D i).chart.symm ((D i).chart (f p.2) - p.1 i)) := by
    rwa [inverse_point_formula D F hown ha i hx hn] at hg
  have hd := (hg'.comp p ((chart_contMDiffAt_symm (D i).chart hD ht).comp p hsub.contMDiffAt)).contDiffAt
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ha
  have hsource : ∀ᶠ q : Space m × ℂ in 𝓝 p, f q.2 ∈ (D i).chart.source :=
    (hf.continuousAt.comp continuous_snd.continuousAt) ((D i).chart.open_source.mem_nhds hx)
  have hnorm : ∀ᶠ q : Space m × ℂ in 𝓝 p, ‖(D i).chart (f q.2) - q.1 i‖ < 1 :=
    (hsub.continuousAt.norm) (isOpen_Iio.mem_nhds hn)
  filter_upwards [hparam, hsource, hnorm] with q hq hqs hqn
  exact congrArg g (inverse_point_formula D F hown hq i hqs hqn)

end VeechDichotomy.AnalyticTransportSmoothCompositions
