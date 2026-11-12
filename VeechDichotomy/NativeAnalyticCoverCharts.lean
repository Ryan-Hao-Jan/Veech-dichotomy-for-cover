module

public import VeechDichotomy.AnalyticCoverTransitionExpressions
public import VeechDichotomy.NativeLocalCoverCriticalCharts

/-! Genuine total-space charts with finite-dimensional complex coordinates
for the moving cover family. Their underlying topology is the original
parameter/source product topology. The regular covering neighborhoods and
the critical neighborhoods are fixed independently of parameters. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open NativeAnalyticMarkTransport ComplexDisplacementParameters AnalyticTransportCoordinates
open Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b)

def transported := AnalyticTransportCoordinates.transport A.combined

omit [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem transported_continuous : Continuous (fun p : Parameters m × X => transported A p.1 p.2) :=
  A.continuous_forward.comp (((productHomeomorph m).continuous.comp continuous_fst).prodMk continuous_snd)

omit [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem transported_inverse_continuous : Continuous (fun p : Parameters m × X => (transported A p.1).symm p.2) :=
  A.continuous_inverse.comp (((productHomeomorph m).continuous.comp continuous_fst).prodMk continuous_snd)

def regular (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) :
    OpenPartialHomeomorph (Parameters m × Y) (Space m × ℂ) :=
  (ParameterizedCoverChart.chart (transported A) (transported_continuous A) (transported_inverse_continuous A)
    (oldLocalMap π y) c).trans ((ComplexDisplacementParameters.chart m).prod (OpenPartialHomeomorph.refl ℂ))

def critical (y : Y) : OpenPartialHomeomorph (Parameters m × Y) (Space m × ℂ) :=
  (ComplexDisplacementParameters.chart m).prod (UniformCriticalNeighborhood.chart π A.uniform y)

theorem regular_apply (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) (p : Parameters m × Y) :
    regular π A y c p = (p.1.val, c (transported A p.1 (π.map p.2))) := by
  refine Prod.ext ?_ ?_
  · rfl
  · exact congrArg c (localMap_apply π (transported A p.1) y p.2)

theorem regular_symm_apply (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) (p : Space m × ℂ) :
    (regular π A y c).symm p = ((ComplexDisplacementParameters.chart m).symm p.1,
      (oldLocalMap π y).symm ((ambientTransport A.combined p.1).symm (c.symm p.2))) := rfl

theorem regular_source (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) (p : Parameters m × Y) :
    p ∈ (regular π A y c).source ↔ p.2 ∈ (oldLocalMap π y).source ∧ transported A p.1 (π.map p.2) ∈ c.source := by
  change (((p.1 ∈ univ ∧ p.2 ∈ (oldLocalMap π y).source) ∧
    (p.1 ∈ univ ∧ transported A p.1 (oldLocalMap π y p.2) ∈ c.source)) ∧
    (p.1 ∈ univ ∧ c (transported A p.1 (oldLocalMap π y p.2)) ∈ univ)) ↔ _
  simp only [mem_univ, true_and, and_true]
  change (_ ∧ localMap π (transported A p.1) y p.2 ∈ c.source) ↔ _
  rw [localMap_apply]
  rfl

theorem regular_target (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) (p : Space m × ℂ) :
    p ∈ (regular π A y c).target ↔ p.1 ∈ domain m ∧ p.2 ∈ c.target ∧
      (ambientTransport A.combined p.1).symm (c.symm p.2) ∈ (oldLocalMap π y).target := by
  change ((p.1 ∈ (ComplexDisplacementParameters.chart m).target ∧ p.2 ∈ univ) ∧
    (((ComplexDisplacementParameters.chart m).symm p.1 ∈ univ ∧ p.2 ∈ c.target) ∧
      ((ComplexDisplacementParameters.chart m).symm p.1 ∈ univ ∧
        (ambientTransport A.combined p.1).symm (c.symm p.2) ∈ (oldLocalMap π y).target))) ↔ _
  simp only [chart_target, mem_univ, and_true, true_and]

theorem critical_apply (y : Y) (p : Parameters m × Y) :
    critical π A y p = (p.1.val, UniformCriticalNeighborhood.chart π A.uniform y p.2) := rfl

theorem regular_inverse_projection (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ)
    (p : Space m × ℂ) (hp : p ∈ (regular π A y c).target) :
    transported A ((regular π A y c).symm p).1 (π.map ((regular π A y c).symm p).2) = c.symm p.2 := by
  have ht := (regular_target π A y c p).mp hp
  have htarget : c.symm p.2 ∈ (localMap π (transported A ((ComplexDisplacementParameters.chart m).symm p.1)) y).target := ht.2.2
  have h := (localMap π (transported A ((ComplexDisplacementParameters.chart m).symm p.1)) y).right_inv htarget
  rw [localMap_apply] at h
  exact h

theorem critical_symm_apply (y : Y) (p : Space m × ℂ) :
    (critical π A y).symm p = ((ComplexDisplacementParameters.chart m).symm p.1,
      (UniformCriticalNeighborhood.chart π A.uniform y).symm p.2) := rfl

theorem critical_target (y : Y) (p : Space m × ℂ) : p ∈ (critical π A y).target ↔
    p.1 ∈ domain m ∧ p.2 ∈ (UniformCriticalNeighborhood.chart π A.uniform y).target := by
  change (_ ∈ (ComplexDisplacementParameters.chart m).target ∧ _) ↔ _
  rw [chart_target]

theorem regular_center (y : RegularPoint π) (a : Parameters m) :
    (a, y.val) ∈ (regular π A y (chartAt ℂ (transported A a (π.map y.val)))).source := by
  rw [regular_source]
  exact ⟨localMap_center π (transported A a) y, mem_chart_source ℂ _⟩

theorem critical_center (hBranch : range b = branchValues π) {y : Y} (hy : y ∈ criticalSet π)
    (a : Parameters m) : (a, y) ∈ (critical π A y).source :=
  ⟨mem_univ a, UniformCriticalNeighborhood.critical_chart_center π A.uniform hBranch hy⟩

end VeechDichotomy.NativeAnalyticCoverCharts
