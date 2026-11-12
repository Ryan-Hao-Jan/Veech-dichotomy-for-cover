module

public import VeechDichotomy.BeltramiPlane
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! The actual complex unit disk with its standard inclusion chart. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiParameter

open BeltramiPlane Set Topology
open scoped Manifold ContDiff

def domain : Set ℂ := {μ | ‖μ‖ < 1}

theorem domain_open : IsOpen domain := isOpen_lt continuous_norm continuous_const

def zero : Parameter := ⟨0, by simp⟩

def chart : OpenPartialHomeomorph Parameter ℂ :=
  (⟨domain, domain_open⟩ : TopologicalSpace.Opens ℂ).openPartialHomeomorphSubtypeCoe ⟨zero⟩

@[simp] theorem chart_apply (μ : Parameter) : chart μ = μ.val := rfl
@[simp] theorem chart_source : chart.source = univ := rfl
@[simp] theorem chart_target : chart.target = domain := TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target _ _

theorem inverse_value {μ : ℂ} (hμ : μ ∈ domain) : (chart.symm μ).val = μ :=
  chart.right_inv (by rwa [chart_target])

instance chartedSpace : ChartedSpace ℂ Parameter := chart.singletonChartedSpace chart_source

instance isComplexManifold (n : ℕ∞ω) : IsManifold 𝓘(ℂ) n Parameter := chart.isManifold_singleton chart_source

end VeechDichotomy.BeltramiParameter
