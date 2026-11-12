module

public import VeechDichotomy.NativeBeltramiTotalSpace

/-! Actual compact native complex curves in each unit-disk fiber. Their
complex atlases are obtained by restricting the proved joint analytic
charts, including at every zero of the original differential. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiSurface

open MNEC.NativeAbelianDifferential BeltramiPlane NativeBeltramiCharts Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure Surface (q : Differential X) (μ : Parameter) where
  point : X

variable (q : Differential X) (μ : Parameter)

instance topology : TopologicalSpace (Surface q μ) := TopologicalSpace.induced Surface.point inferInstance

def toOriginal : Surface q μ ≃ₜ X where
  toFun := Surface.point
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (Surface q μ) := (toOriginal q μ).isEmbedding.t2Space
instance compactSpace : CompactSpace (Surface q μ) := (toOriginal q μ).symm.compactSpace
instance connectedSpace : ConnectedSpace (Surface q μ) :=
  (toOriginal q μ).symm.surjective.connectedSpace (toOriginal q μ).symm.continuous

def chart (i : Surface q μ) : OpenPartialHomeomorph (Surface q μ) ℂ :=
  (toOriginal q μ).transOpenPartialHomeomorph ((powerAt q i.point).chart.transHomeomorph
    (BeltramiPowerLift.rootHomeomorph μ (powerAt q i.point).exponent (powerAt q i.point).exponent_pos))

theorem chart_source (i y : Surface q μ) : y ∈ (chart q μ i).source ↔ y.point ∈ (powerAt q i.point).chart.source := Iff.rfl

theorem chart_center (i : Surface q μ) : i ∈ (chart q μ i).source := (powerAt q i.point).center

theorem chart_center_zero (i : Surface q μ) : chart q μ i i = 0 := by
  change BeltramiPowerLift.rootHomeomorph μ _ _ ((powerAt q i.point).chart i.point) = 0
  rw [(powerAt q i.point).center_zero, BeltramiPowerLift.rootHomeomorph_zero]

theorem chart_value (i y : Surface q μ) :
    NativeBeltramiCharts.chart q i.point (μ, y.point) = (μ.val, chart q μ i y) := rfl

theorem parameter_inverse : BeltramiParameter.chart.symm μ.val = μ :=
  BeltramiParameter.chart.left_inv (mem_univ μ)

theorem total_target (i : Surface q μ) {z : ℂ} (hz : z ∈ (chart q μ i).target) :
    (μ.val, z) ∈ (NativeBeltramiCharts.chart q i.point).target := by
  rw [NativeBeltramiCharts.chart_target, parameter_inverse]
  exact ⟨μ.property, hz⟩

theorem inverse_value (i : Surface q μ) (z : ℂ) :
    (NativeBeltramiCharts.chart q i.point).symm (μ.val, z) = (μ, ((chart q μ i).symm z).point) := by
  rw [NativeBeltramiCharts.chart_symm_apply, parameter_inverse]
  rfl

theorem transition_value (i j : Surface q μ) (z : ℂ) :
    (((NativeBeltramiCharts.chart q i.point).symm.trans (NativeBeltramiCharts.chart q j.point)) (μ.val, z)).2 =
      ((chart q μ i).symm.trans (chart q μ j)) z := by
  rw [OpenPartialHomeomorph.trans_apply, inverse_value]
  rfl

theorem total_transition_source (i j : Surface q μ) {z : ℂ}
    (hz : z ∈ ((chart q μ i).symm.trans (chart q μ j)).source) :
    (μ.val, z) ∈ ((NativeBeltramiCharts.chart q i.point).symm.trans (NativeBeltramiCharts.chart q j.point)).source := by
  refine ⟨total_target q μ i hz.1, ?_⟩
  change ((NativeBeltramiCharts.chart q i.point).symm (μ.val, z)) ∈ (NativeBeltramiCharts.chart q j.point).source
  rw [inverse_value, NativeBeltramiCharts.chart_source]
  exact hz.2

theorem transition_contDiffAt (i j : Surface q μ) (z : ℂ)
    (hz : z ∈ ((chart q μ i).symm.trans (chart q μ j)).source) :
    ContDiffAt ℂ ω ((chart q μ i).symm.trans (chart q μ j)) z := by
  have htotal := NativeBeltramiTransitions.transition_contDiffAt q i.point j.point (μ.val, z)
    (total_transition_source q μ i j hz)
  have hslice : ContDiffAt ℂ ω (fun w : ℂ => (μ.val, w)) z := contDiffAt_const.prodMk contDiffAt_id
  have h := contDiffAt_snd.comp z (htotal.comp z hslice)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun w => (transition_value q μ i j w).symm

theorem transition_power_germ (i j : Surface q μ) (z : ℂ)
    (hz : z ∈ ((chart q μ i).symm.trans (chart q μ j)).source) :
    ∃ c : ℂ, ∀ᶠ w in 𝓝 z, (((chart q μ i).symm.trans (chart q μ j)) w) ^ (powerAt q j.point).exponent =
      w ^ (powerAt q i.point).exponent + c := by
  obtain ⟨c, hc⟩ := NativeBeltramiTransitions.transition_power_germ q i.point j.point (μ.val, z)
    (total_transition_source q μ i j hz)
  have hnear := (continuous_const.prodMk continuous_id).continuousAt hc
  refine ⟨c + μ.val * star c, ?_⟩
  filter_upwards [hnear] with w hw
  change (((NativeBeltramiCharts.chart q i.point).symm.trans (NativeBeltramiCharts.chart q j.point))
    (μ.val, w)).2 ^ (powerAt q j.point).exponent = w ^ (powerAt q i.point).exponent + c + μ.val * star c at hw
  rw [transition_value] at hw
  simpa only [add_assoc] using hw

@[instance_reducible] def chartedSpace : ChartedSpace ℂ (Surface q μ) where
  atlas := range (chart q μ)
  chartAt := chart q μ
  mem_chart_source := chart_center q μ
  chart_mem_atlas i := ⟨i, rfl⟩

theorem isComplexManifold : letI := chartedSpace q μ
    IsManifold 𝓘(ℂ) ω (Surface q μ) := by
  let := chartedSpace q μ
  let : HasGroupoid (Surface q μ) (contDiffGroupoid ω 𝓘(ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ))
    intro e f he hf
    change e ∈ range (chart q μ) at he
    change f ∈ range (chart q μ) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    have hdiff : ContDiffOn ℂ ω ((chart q μ i).symm.trans (chart q μ j))
        ((chart q μ i).symm.trans (chart q μ j)).source :=
      fun z hz => (transition_contDiffAt q μ i j z hz).contDiffWithinAt
    simpa only [contDiffPregroupoid, mfld_simps] using hdiff
  exact IsManifold.mk' 𝓘(ℂ) ω (Surface q μ)

attribute [instance] chartedSpace isComplexManifold

end VeechDichotomy.NativeBeltramiSurface
