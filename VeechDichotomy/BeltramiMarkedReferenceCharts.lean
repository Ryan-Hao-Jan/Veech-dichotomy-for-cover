module

public import VeechDichotomy.ComplexBeltramiMarkParameters
public import VeechDichotomy.NativeBeltramiTotalSpace

/-! Actual reference-family charts retaining both the deformation
parameter and every displacement parameter. Their topology is the
original parameter/surface product topology. The additional displacements
do not change the reference fiber complex structure. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedReferenceCharts

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data qX b μ₀)

def parameter (a : ComplexBeltramiMarkParameters.Parameters A) : Parameter :=
  (ComplexBeltramiMarkParameters.productHomeomorph A a).1.val

theorem parameter_value (a : ComplexBeltramiMarkParameters.Parameters A) : (parameter A a).val = a.val.1 := rfl

theorem continuous_parameter : Continuous (parameter A) :=
  continuous_subtype_val.comp (continuous_fst.comp (ComplexBeltramiMarkParameters.productHomeomorph A).continuous)

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (qY : Differential Y)

def plane (y : Y) (a : ComplexBeltramiMarkParameters.Parameters A) : ℂ ≃ₜ ℂ :=
  BeltramiPowerLift.rootHomeomorph (parameter A a)
    (NativePowerCharts.chosen qY y).exponent (NativePowerCharts.chosen qY y).exponent_pos

theorem continuous_plane (y : Y) :
    Continuous (fun p : ComplexBeltramiMarkParameters.Parameters A × ℂ => plane A qY y p.1 p.2) :=
  Continuous.comp (f := fun p : ComplexBeltramiMarkParameters.Parameters A × ℂ => (parameter A p.1, p.2))
    (g := fun p : Parameter × ℂ => BeltramiPowerLift.rootHomeomorph p.1
      (NativePowerCharts.chosen qY y).exponent (NativePowerCharts.chosen qY y).exponent_pos p.2)
    (BeltramiPowerLift.continuous_forward (NativePowerCharts.chosen qY y).exponent_pos)
    (((continuous_parameter A).comp continuous_fst).prodMk continuous_snd)

theorem continuous_plane_inverse (y : Y) :
    Continuous (fun p : ComplexBeltramiMarkParameters.Parameters A × ℂ => (plane A qY y p.1).symm p.2) :=
  Continuous.comp (f := fun p : ComplexBeltramiMarkParameters.Parameters A × ℂ => (parameter A p.1, p.2))
    (g := fun p : Parameter × ℂ => (BeltramiPowerLift.rootHomeomorph p.1
      (NativePowerCharts.chosen qY y).exponent (NativePowerCharts.chosen qY y).exponent_pos).symm p.2)
    (BeltramiPowerLift.continuous_inverse (NativePowerCharts.chosen qY y).exponent_pos)
    (((continuous_parameter A).comp continuous_fst).prodMk continuous_snd)

def chart (y : Y) : OpenPartialHomeomorph (ComplexBeltramiMarkParameters.Parameters A × Y)
    (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :=
  (ParameterizedCoverChart.chart (plane A qY y) (continuous_plane A qY y) (continuous_plane_inverse A qY y)
    (NativePowerCharts.chosen qY y).chart (OpenPartialHomeomorph.refl ℂ)).trans
      ((ComplexBeltramiMarkParameters.chart A).prod (OpenPartialHomeomorph.refl ℂ))

theorem chart_apply (y : Y) (p : ComplexBeltramiMarkParameters.Parameters A × Y) :
    chart A qY y p = (p.1.val, plane A qY y p.1 ((NativePowerCharts.chosen qY y).chart p.2)) := rfl

theorem chart_symm_apply (y : Y) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :
    (chart A qY y).symm p = ((ComplexBeltramiMarkParameters.chart A).symm p.1,
      (NativePowerCharts.chosen qY y).chart.symm
        ((plane A qY y ((ComplexBeltramiMarkParameters.chart A).symm p.1)).symm p.2)) := rfl

theorem chart_source (y : Y) (p : ComplexBeltramiMarkParameters.Parameters A × Y) :
    p ∈ (chart A qY y).source ↔ p.2 ∈ (NativePowerCharts.chosen qY y).chart.source := by
  change (((p.1 ∈ univ ∧ p.2 ∈ (NativePowerCharts.chosen qY y).chart.source) ∧
    (p.1 ∈ univ ∧ _ ∈ univ)) ∧ (p.1 ∈ univ ∧ _ ∈ univ)) ↔ _
  simp only [mem_univ, true_and, and_true]

theorem chart_target (y : Y) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :
    p ∈ (chart A qY y).target ↔ p.1 ∈ ComplexBeltramiMarkParameters.domain A ∧
      (plane A qY y ((ComplexBeltramiMarkParameters.chart A).symm p.1)).symm p.2 ∈
        (NativePowerCharts.chosen qY y).chart.target := by
  change ((p.1 ∈ (ComplexBeltramiMarkParameters.chart A).target ∧ p.2 ∈ univ) ∧
    (((ComplexBeltramiMarkParameters.chart A).symm p.1 ∈ univ ∧ p.2 ∈ univ) ∧
      ((ComplexBeltramiMarkParameters.chart A).symm p.1 ∈ univ ∧ _ ∈ (NativePowerCharts.chosen qY y).chart.target))) ↔ _
  simp only [ComplexBeltramiMarkParameters.chart_target, mem_univ, true_and, and_true]
  rfl

theorem chart_center (a : ComplexBeltramiMarkParameters.Parameters A) (y : Y) :
    (a, y) ∈ (chart A qY y).source := (chart_source A qY y _).mpr (NativePowerCharts.chosen qY y).center

def realization (p : ComplexBeltramiMarkParameters.Parameters A × Y) : NativeBeltramiTotalSpace.TotalSpace qY :=
  ⟨(parameter A p.1, p.2)⟩

theorem continuous_realization : Continuous (realization A qY) :=
  (NativeBeltramiTotalSpace.toProduct qY).symm.continuous.comp
    (((continuous_parameter A).comp continuous_fst).prodMk continuous_snd)

theorem native_chart_value (y : Y) (p : ComplexBeltramiMarkParameters.Parameters A × Y) :
    NativeBeltramiTotalSpace.chart qY ⟨(μ₀, y)⟩ (realization A qY p) =
      ((chart A qY y p).1.1, (chart A qY y p).2) := rfl

theorem inverse_parameter (y : Y) {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ}
    (hp : p ∈ (chart A qY y).target) : ((chart A qY y).symm p).1.val = p.1 :=
  ComplexBeltramiMarkParameters.inverse_value A ((chart_target A qY y p).mp hp).1

theorem realization_inverse (y : Y) {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ}
    (hp : p ∈ (chart A qY y).target) :
    realization A qY ((chart A qY y).symm p) = (NativeBeltramiTotalSpace.chart qY ⟨(μ₀, y)⟩).symm (p.1.1, p.2) := by
  let c := NativeBeltramiTotalSpace.chart qY ⟨(μ₀, y)⟩
  have hsrc : realization A qY ((chart A qY y).symm p) ∈ c.source :=
    (NativeBeltramiCharts.chart_source qY y _).mpr
      ((chart_source A qY y _).mp ((chart A qY y).map_target hp))
  have hvalue : c (realization A qY ((chart A qY y).symm p)) = (p.1.1, p.2) := by
    rw [native_chart_value, (chart A qY y).right_inv hp]
  calc
    realization A qY ((chart A qY y).symm p) = c.symm (c (realization A qY ((chart A qY y).symm p))) := (c.left_inv hsrc).symm
    _ = c.symm (p.1.1, p.2) := congrArg c.symm hvalue

end VeechDichotomy.BeltramiMarkedReferenceCharts
