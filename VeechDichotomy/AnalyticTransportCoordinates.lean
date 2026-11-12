module

public import VeechDichotomy.ComplexDisplacementParameters
public import VeechDichotomy.DisjointPointTransportUniform
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! In actual complex displacement coordinates, the combined disjoint
transports and their inverses have jointly holomorphic translation formulas
on their marked inner disks. The inverse formula is proved explicitly,
so parameter-dependent inverse calculus needs no extra existence premise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.AnalyticTransportCoordinates

open Set Filter Metric Topology LocalTranslationPlane PointTransportDisk
open ComplexDisplacementParameters PointTransportUniform DisjointPointTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] {m : ℕ}
variable (D : Fin m → Disk (X := X)) (F : (Fin m → Parameter) → X ≃ₜ X)
  (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)

def transport (a : Parameters m) : X ≃ₜ X := F (productHomeomorph m a)

def ambientTransport (a : Space m) : X ≃ₜ X := transport F ((ComplexDisplacementParameters.chart m).symm a)

theorem ambient_parameter_value {a : Space m} (ha : a ∈ domain m) (i : Fin m) :
    (productHomeomorph m ((ComplexDisplacementParameters.chart m).symm a) i).val = a i := by
  change ((ComplexDisplacementParameters.chart m).symm a).val i = a i
  rw [inverse_value m ha]

include hown in

theorem forward_formula {a : Space m} (ha : a ∈ domain m) (i : Fin m) {z : ℂ} (hz : ‖z‖ < 1) :
    ambientTransport F a ((D i).chart.symm z) = (D i).chart.symm (z + a i) := by
  have hzT : z ∈ (D i).chart.target := (D i).closedBall_target (by
    rw [mem_closedBall, dist_zero_right]
    linarith)
  have hx : (D i).chart.symm z ∈ innerDisk (D i) := by
    refine ⟨(D i).chart.map_target hzT, ?_⟩
    rw [mem_preimage, (D i).chart.right_inv hzT]
    simpa only [mem_ball, dist_zero_right] using hz
  have hsup := support_mem_nhds (D i) hx.1 (lt_trans (innerDisk_norm (D i) hx) (by norm_num))
  rw [ambientTransport, transport, hown i _ _ (mem_of_mem_nhds hsup), transport_value (D i) _ hx,
    (D i).chart.right_inv hzT, ambient_parameter_value ha i]

include hown in
theorem inverse_formula {a : Space m} (ha : a ∈ domain m) (i : Fin m) {w : ℂ}
    (hw : ‖w - a i‖ < 1) :
    (ambientTransport F a).symm ((D i).chart.symm w) = (D i).chart.symm (w - a i) := by
  apply (ambientTransport F a).injective
  rw [Homeomorph.apply_symm_apply, forward_formula D F hown ha i hw, sub_add_cancel]

variable [ChartedSpace ℂ X]

omit [T2Space X] in
theorem translated_expression_differentiableAt (i : Fin m) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (harg : p.2 + p.1 i ∈ (D i).chart.target)
    (hout : (D i).chart.symm (p.2 + p.1 i) ∈ c.source) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => c ((D i).chart.symm (q.2 + q.1 i))) p := by
  have heval : DifferentiableAt ℂ (fun q : Space m × ℂ => q.1 i) p :=
    ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).differentiableAt).comp p differentiableAt_fst
  have hsum := differentiableAt_snd.add heval
  exact ((hc.mdifferentiableAt hout).comp p
    ((hD.mdifferentiableAt_symm harg).comp p hsum.mdifferentiableAt)).differentiableAt

omit [T2Space X] in
theorem inverse_expression_differentiableAt (i : Fin m) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (harg : p.2 - p.1 i ∈ (D i).chart.target)
    (hout : (D i).chart.symm (p.2 - p.1 i) ∈ c.source) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => c ((D i).chart.symm (q.2 - q.1 i))) p := by
  have heval : DifferentiableAt ℂ (fun q : Space m × ℂ => q.1 i) p :=
    ((ContinuousLinearMap.proj i : Space m →L[ℂ] ℂ).differentiableAt).comp p differentiableAt_fst
  have hsub := differentiableAt_snd.sub heval
  exact ((hc.mdifferentiableAt hout).comp p
    ((hD.mdifferentiableAt_symm harg).comp p hsub.mdifferentiableAt)).differentiableAt

include hown in
theorem forward_differentiableAt (i : Fin m) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (ha : p.1 ∈ domain m) (hz : ‖p.2‖ < 1)
    (harg : p.2 + p.1 i ∈ (D i).chart.target) (hout : (D i).chart.symm (p.2 + p.1 i) ∈ c.source) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => c (ambientTransport F q.1 ((D i).chart.symm q.2))) p := by
  apply (translated_expression_differentiableAt D i c hc hD p harg hout).congr_of_eventuallyEq
  have hparam := (domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))
  have hcoord : IsOpen {q : Space m × ℂ | ‖q.2‖ < 1} := isOpen_lt continuous_snd.norm continuous_const
  filter_upwards [hparam.mem_nhds ha, hcoord.mem_nhds hz] with q hq hqz
  exact congrArg c (forward_formula D F hown hq i hqz)

include hown in
theorem inverse_differentiableAt (i : Fin m) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (hD : (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (ha : p.1 ∈ domain m) (hw : ‖p.2 - p.1 i‖ < 1)
    (harg : p.2 - p.1 i ∈ (D i).chart.target) (hout : (D i).chart.symm (p.2 - p.1 i) ∈ c.source) :
    DifferentiableAt ℂ (fun q : Space m × ℂ => c ((ambientTransport F q.1).symm ((D i).chart.symm q.2))) p := by
  apply (inverse_expression_differentiableAt D i c hc hD p harg hout).congr_of_eventuallyEq
  have hparam := (domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))
  have hcoord : IsOpen {q : Space m × ℂ | ‖q.2 - q.1 i‖ < 1} :=
    isOpen_lt (continuous_snd.sub ((continuous_apply i).comp continuous_fst)).norm continuous_const
  filter_upwards [hparam.mem_nhds ha, hcoord.mem_nhds hw] with q hq hqw
  exact congrArg c (inverse_formula D F hown hq i hqw)

end VeechDichotomy.AnalyticTransportCoordinates
