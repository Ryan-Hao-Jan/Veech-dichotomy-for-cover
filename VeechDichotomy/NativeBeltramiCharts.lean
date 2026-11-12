module

public import VeechDichotomy.BeltramiParameter
public import VeechDichotomy.BeltramiPowerLift
public import VeechDichotomy.NativePowerCharts
public import VeechDichotomy.ParameterizedCoverChart
public import MNEC.NativeLocalPrimitives

/-! Actual total charts for the unit-disk deformation of a native
differential. Their source neighborhoods are fixed, and both chart maps
are jointly continuous at all zeros as well as regular points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCharts

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev powerAt (q : Differential X) (i : X) := NativePowerCharts.chosen q i

def chart (q : Differential X) (i : X) : OpenPartialHomeomorph (Parameter × X) (ℂ × ℂ) :=
  (ParameterizedCoverChart.chart
    (fun μ => BeltramiPowerLift.rootHomeomorph μ (powerAt q i).exponent (powerAt q i).exponent_pos)
    (BeltramiPowerLift.continuous_forward (powerAt q i).exponent_pos)
    (BeltramiPowerLift.continuous_inverse (powerAt q i).exponent_pos)
    (powerAt q i).chart (OpenPartialHomeomorph.refl ℂ)).trans
    (BeltramiParameter.chart.prod (OpenPartialHomeomorph.refl ℂ))

theorem chart_apply (q : Differential X) (i : X) (p : Parameter × X) :
    chart q i p = (p.1.val, BeltramiPowerLift.rootHomeomorph p.1 (powerAt q i).exponent
      (powerAt q i).exponent_pos ((powerAt q i).chart p.2)) := rfl

theorem chart_symm_apply (q : Differential X) (i : X) (p : ℂ × ℂ) :
    (chart q i).symm p = (BeltramiParameter.chart.symm p.1,
      (powerAt q i).chart.symm ((BeltramiPowerLift.rootHomeomorph (BeltramiParameter.chart.symm p.1)
        (powerAt q i).exponent (powerAt q i).exponent_pos).symm p.2)) := rfl

theorem chart_source (q : Differential X) (i : X) (p : Parameter × X) :
    p ∈ (chart q i).source ↔ p.2 ∈ (powerAt q i).chart.source := by
  change (((p.1 ∈ univ ∧ p.2 ∈ (powerAt q i).chart.source) ∧
      (p.1 ∈ univ ∧ _ ∈ univ)) ∧ (p.1 ∈ univ ∧ _ ∈ univ)) ↔ _
  simp only [mem_univ, true_and, and_true]

theorem chart_target (q : Differential X) (i : X) (p : ℂ × ℂ) : p ∈ (chart q i).target ↔
    p.1 ∈ BeltramiParameter.domain ∧
      (BeltramiPowerLift.rootHomeomorph (BeltramiParameter.chart.symm p.1)
        (powerAt q i).exponent (powerAt q i).exponent_pos).symm p.2 ∈ (powerAt q i).chart.target := by
  change ((p.1 ∈ BeltramiParameter.chart.target ∧ p.2 ∈ univ) ∧
    (((BeltramiParameter.chart.symm p.1) ∈ univ ∧ p.2 ∈ univ) ∧
      ((BeltramiParameter.chart.symm p.1) ∈ univ ∧ _ ∈ (powerAt q i).chart.target))) ↔ _
  simp only [BeltramiParameter.chart_target, mem_univ, and_true, true_and]
  rfl

theorem chart_center (q : Differential X) (i : X) (μ : Parameter) : (μ, i) ∈ (chart q i).source :=
  (chart_source q i (μ, i)).mpr (powerAt q i).center

theorem chart_center_zero (q : Differential X) (i : X) (μ : Parameter) : (chart q i (μ, i)).2 = 0 := by
  rw [chart_apply, (powerAt q i).center_zero, BeltramiPowerLift.rootHomeomorph_zero]

theorem chart_zero_iff (q : Differential X) (i : X) (p : Parameter × X) (hp : p ∈ (chart q i).source) :
    (chart q i p).2 = 0 ↔ p.2 = i := by
  constructor
  · intro h
    have hroot : (chart q i p).2 = (chart q i (p.1, i)).2 := h.trans (chart_center_zero q i p.1).symm
    have heq := (chart q i).injOn hp (chart_center q i p.1) (Prod.ext rfl hroot)
    exact congrArg Prod.snd heq
  · intro h
    have hpEq : p = (p.1, i) := Prod.ext rfl h
    rw [hpEq]
    exact chart_center_zero q i p.1

theorem chart_power (q : Differential X) (i : X) (p : Parameter × X) :
    (chart q i p).2 ^ (powerAt q i).exponent = BeltramiPlane.map p.1.val
      ((powerAt q i).chart p.2 ^ (powerAt q i).exponent) :=
  BeltramiPowerLift.rootHomeomorph_pow p.1 (powerAt q i).exponent_pos _

theorem primitive_difference (q : Differential X) (i j x : X)
    (hxi : x ∈ (powerAt q i).chart.source) (hxj : x ∈ (powerAt q j).chart.source) :
    ∃ c : ℂ, ∀ᶠ y in 𝓝 x, (powerAt q j).chart y ^ (powerAt q j).exponent =
      (powerAt q i).chart y ^ (powerAt q i).exponent + c :=
  ⟨_, MNEC.NativeLocalPrimitives.difference_germ q
    (fun y => (powerAt q i).chart y ^ (powerAt q i).exponent)
    (fun y => (powerAt q j).chart y ^ (powerAt q j).exponent)
    (powerAt q i).chart.source (powerAt q j).chart.source
    (powerAt q i).chart.open_source (powerAt q j).chart.open_source
    (powerAt q i).primitive_derivative (powerAt q j).primitive_derivative x ⟨hxi, hxj⟩⟩

end VeechDichotomy.NativeBeltramiCharts
