module

public import VeechDichotomy.AnalyticTransportCoordinates

/-! Joint holomorphic dependence survives composition with native
holomorphic curve maps in either direction. The inverse is computed by
subtracting the same complex displacement inside its marked chart. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.AnalyticTransportCompositions

open Set Filter Metric Topology LocalTranslationPlane PointTransportDisk
open ComplexDisplacementParameters PointTransportUniform AnalyticTransportCoordinates
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] {m : ℕ}
variable (D : Fin m → Disk (X := X)) (F : (Fin m → Parameter) → X ≃ₜ X)
  (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)

include hown in
theorem forward_point_formula {a : Space m} (ha : a ∈ domain m) (i : Fin m) {x : X}
    (hx : x ∈ innerDisk (D i)) :
    ambientTransport F a x = (D i).chart.symm ((D i).chart x + a i) := by
  have h := forward_formula D F hown ha i (innerDisk_norm (D i) hx)
  rwa [(D i).chart.left_inv hx.1] at h

include hown in
theorem inverse_point_formula {a : Space m} (ha : a ∈ domain m) (i : Fin m) {x : X}
    (hx : x ∈ (D i).chart.source) (hn : ‖(D i).chart x - a i‖ < 1) :
    (ambientTransport F a).symm x = (D i).chart.symm ((D i).chart x - a i) := by
  have h := inverse_formula D F hown ha i hn
  rwa [(D i).chart.left_inv hx] at h

include hown in
theorem image_conditions {a : Space m} (ha : a ∈ domain m) (i : Fin m) {x : X}
    (hx : x ∈ innerDisk (D i)) :
    ambientTransport F a x ∈ (D i).chart.source ∧
      ‖(D i).chart (ambientTransport F a x) - a i‖ < 1 := by
  have ht : (D i).chart x + a i ∈ (D i).chart.target := translated_target (D i) ⟨a i, ha i⟩ hx
  rw [forward_point_formula D F hown ha i hx]
  refine ⟨(D i).chart.map_target ht, ?_⟩
  rw [(D i).chart.right_inv ht, add_sub_cancel_right]
  exact innerDisk_norm (D i) hx

omit [T2Space X] in
theorem evaluation_differentiableAt (i : Fin m) (p : Space m × ℂ) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => q.1 i) p :=
  ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).differentiableAt).comp p differentiableAt_fst

variable [ChartedSpace ℂ X]

include hown in
theorem forward_differentiableAt (i : Fin m) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (f : ℂ → X) (g : X → ℂ) (p : Space m × ℂ) (ha : p.1 ∈ domain m)
    (hx : f p.2 ∈ innerDisk (D i)) (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p.2)
    (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (ambientTransport F p.1 (f p.2))) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => g (ambientTransport F q.1 (f q.2))) p := by
  have hv := ((hD.mdifferentiableAt hx.1).comp p.2 hf).differentiableAt
  have hsum := (hv.comp p differentiableAt_snd).add (evaluation_differentiableAt i p)
  have ht : (D i).chart (f p.2) + p.1 i ∈ (D i).chart.target :=
    translated_target (D i) ⟨p.1 i, ha i⟩ hx
  have hg' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g ((D i).chart.symm ((D i).chart (f p.2) + p.1 i)) := by
    rwa [forward_point_formula D F hown ha i hx] at hg
  have hd := (hg'.comp p ((hD.mdifferentiableAt_symm ht).comp p hsum.mdifferentiableAt)).differentiableAt
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ha
  have hinner : ∀ᶠ q : Space m × ℂ in 𝓝 p, f q.2 ∈ innerDisk (D i) :=
    (hf.continuousAt.comp continuous_snd.continuousAt) ((innerDisk_open (D i)).mem_nhds hx)
  filter_upwards [hparam, hinner] with q hq hqi
  exact congrArg g (forward_point_formula D F hown hq i hqi)

include hown in
theorem inverse_differentiableAt (i : Fin m) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (f : ℂ → X) (g : X → ℂ) (p : Space m × ℂ) (ha : p.1 ∈ domain m)
    (hx : f p.2 ∈ (D i).chart.source) (hn : ‖(D i).chart (f p.2) - p.1 i‖ < 1)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p.2)
    (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g ((ambientTransport F p.1).symm (f p.2))) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => g ((ambientTransport F q.1).symm (f q.2))) p := by
  have hv := ((hD.mdifferentiableAt hx).comp p.2 hf).differentiableAt
  have hsub := (hv.comp p differentiableAt_snd).sub (evaluation_differentiableAt i p)
  have ht : (D i).chart (f p.2) - p.1 i ∈ (D i).chart.target := (D i).closedBall_target (by
    rw [mem_closedBall, dist_zero_right]
    linarith)
  have hg' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g ((D i).chart.symm ((D i).chart (f p.2) - p.1 i)) := by
    rwa [inverse_point_formula D F hown ha i hx hn] at hg
  have hd := (hg'.comp p ((hD.mdifferentiableAt_symm ht).comp p hsub.mdifferentiableAt)).differentiableAt
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ha
  have hsource : ∀ᶠ q : Space m × ℂ in 𝓝 p, f q.2 ∈ (D i).chart.source :=
    (hf.continuousAt.comp continuous_snd.continuousAt) ((D i).chart.open_source.mem_nhds hx)
  have hnorm : ∀ᶠ q : Space m × ℂ in 𝓝 p, ‖(D i).chart (f q.2) - q.1 i‖ < 1 :=
    (hsub.continuousAt.norm) (isOpen_Iio.mem_nhds hn)
  filter_upwards [hparam, hsource, hnorm] with q hq hqs hqn
  exact congrArg g (inverse_point_formula D F hown hq i hqs hqn)

end VeechDichotomy.AnalyticTransportCompositions
