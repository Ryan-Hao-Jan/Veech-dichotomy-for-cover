module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! The actual nonzero complex scalars with the standard open-subset
complex structure and holomorphic value coordinate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NonzeroComplexParameter

open Set Topology
open scoped Manifold ContDiff

abbrev Parameter := {c : ℂ // c ≠ 0}

def domain : Set ℂ := {c | c ≠ 0}

theorem domain_open : IsOpen domain := isClosed_singleton.isOpen_compl

def one : Parameter := ⟨1, one_ne_zero⟩

def chart : OpenPartialHomeomorph Parameter ℂ :=
  (⟨domain, domain_open⟩ : TopologicalSpace.Opens ℂ).openPartialHomeomorphSubtypeCoe ⟨one⟩

@[simp] theorem chart_apply (c : Parameter) : chart c = c.val := rfl
@[simp] theorem chart_source : chart.source = univ := rfl
@[simp] theorem chart_target : chart.target = domain := TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target _ _

instance chartedSpace : ChartedSpace ℂ Parameter := chart.singletonChartedSpace chart_source
instance isComplexManifold (n : ℕ∞ω) : IsManifold 𝓘(ℂ) n Parameter := chart.isManifold_singleton chart_source

theorem value_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : Parameter → ℂ) := by
  intro c
  exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) (mem_univ c)

end VeechDichotomy.NonzeroComplexParameter
