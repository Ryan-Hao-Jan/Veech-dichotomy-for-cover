module

public import VeechDichotomy.NativeAnalyticCoverCharts

/-! Analytic compatibility of the actual total-space cover-family charts.
All four regular/critical transition cases are proved in the full complex
parameter-and-curve coordinate space, not just separately in each fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverTransitions

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open NativeAnalyticMarkTransport ComplexDisplacementParameters NativeAnalyticCoverCharts
open AnalyticTransportCoordinates HolomorphicCurveGerms Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b)

theorem critical_regular (i : Y) (j : RegularPoint π) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (p : Space m × ℂ)
    (hp : p ∈ ((critical π A i).symm.trans (regular π A j c)).source) :
    ContDiffAt ℂ ω ((critical π A i).symm.trans (regular π A j c)) p := by
  let e := UniformCriticalNeighborhood.chart π A.uniform i
  have ht := (critical_target π A i p).mp hp.1
  have he : e.symm p.2 ∈ e.source := e.map_target ht.2
  have hregion := interior_subset he.2
  change π.map (e.symm p.2) ∈ ⋃ k, PointTransportUniform.innerDisk (A.disks k) at hregion
  obtain ⟨k, hk⟩ := mem_iUnion.mp hregion
  have hout := ((regular_source π A j c ((critical π A i).symm p)).mp hp.2).2
  have hd := AnalyticCoverTransitionExpressions.forward_contDiffAt π A e c
    (UniformCriticalNeighborhood.chart_mdifferentiable π A.uniform i) hc p ht.1 ht.2 k hk hout
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ht.1
  filter_upwards [hparam] with q hq
  rw [OpenPartialHomeomorph.trans_apply, regular_apply]
  refine Prod.ext ?_ ?_
  · exact inverse_value m hq
  · rfl

theorem regular_critical (i : RegularPoint π) (c : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (j : Y) (p : Space m × ℂ)
    (hp : p ∈ ((regular π A i c).symm.trans (critical π A j)).source) :
    ContDiffAt ℂ ω ((regular π A i c).symm.trans (critical π A j)) p := by
  let e := UniformCriticalNeighborhood.chart π A.uniform j
  have ht := (regular_target π A i c p).mp hp.1
  have he : (oldLocalMap π i).symm ((ambientTransport A.combined p.1).symm (c.symm p.2)) ∈ e.source := hp.2.2
  have hregion := interior_subset he.2
  change π.map ((oldLocalMap π i).symm ((ambientTransport A.combined p.1).symm (c.symm p.2))) ∈
      ⋃ k, PointTransportUniform.innerDisk (A.disks k) at hregion
  obtain ⟨k, hk⟩ := mem_iUnion.mp hregion
  have hd := AnalyticCoverTransitionExpressions.inverse_contDiffAt π A i e c
    (UniformCriticalNeighborhood.chart_mdifferentiable π A.uniform j) hc p ht.1 ht.2.1 ht.2.2 he k hk
  apply hd.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ht.1
  filter_upwards [hparam] with q hq
  rw [OpenPartialHomeomorph.trans_apply, critical_apply]
  refine Prod.ext ?_ ?_
  · exact inverse_value m hq
  · rfl

theorem regular_regular (i j : RegularPoint π) (c d : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (hd : d.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (p : Space m × ℂ)
    (hp : p ∈ ((regular π A i c).symm.trans (regular π A j d)).source) :
    ContDiffAt ℂ ω ((regular π A i c).symm.trans (regular π A j d)) p := by
  have ht := (regular_target π A i c p).mp hp.1
  have hout := ((regular_source π A j d ((regular π A i c).symm p)).mp hp.2).2
  rw [regular_inverse_projection π A i c p hp.1] at hout
  have hscalar := ((chart_contMDiffAt d hd hout).comp p.2 (chart_contMDiffAt_symm c hc ht.2.1)).contDiffAt
  have hproduct : ContDiffAt ℂ ω (fun q : Space m × ℂ => (q.1, d (c.symm q.2))) p :=
    contDiffAt_fst.prodMk (hscalar.comp p contDiffAt_snd)
  apply hproduct.congr_of_eventuallyEq
  filter_upwards [(regular π A i c).open_target.mem_nhds hp.1] with q hq
  rw [OpenPartialHomeomorph.trans_apply, regular_apply]
  refine Prod.ext ?_ ?_
  · exact inverse_value m ((regular_target π A i c q).mp hq).1
  · exact congrArg d (regular_inverse_projection π A i c q hq)

theorem critical_critical (i j : Y) (p : Space m × ℂ)
    (hp : p ∈ ((critical π A i).symm.trans (critical π A j)).source) :
    ContDiffAt ℂ ω ((critical π A i).symm.trans (critical π A j)) p := by
  let c := UniformCriticalNeighborhood.chart π A.uniform i
  let d := UniformCriticalNeighborhood.chart π A.uniform j
  have ht := (critical_target π A i p).mp hp.1
  have hout : c.symm p.2 ∈ d.source := hp.2.2
  have hscalar := ((chart_contMDiffAt d (UniformCriticalNeighborhood.chart_mdifferentiable π A.uniform j) hout).comp p.2
    (chart_contMDiffAt_symm c (UniformCriticalNeighborhood.chart_mdifferentiable π A.uniform i) ht.2)).contDiffAt
  have hproduct : ContDiffAt ℂ ω (fun q : Space m × ℂ => (q.1, d (c.symm q.2))) p :=
    contDiffAt_fst.prodMk (hscalar.comp p contDiffAt_snd)
  apply hproduct.congr_of_eventuallyEq
  have hparam := ((domain_open m).preimage (continuous_fst : Continuous (fun q : Space m × ℂ => q.1))).mem_nhds ht.1
  filter_upwards [hparam] with q hq
  exact Prod.ext (inverse_value m hq) rfl

def rawChart (p : Parameters m × Y) : OpenPartialHomeomorph (Parameters m × Y) (Space m × ℂ) := by
  classical
  exact if hy : p.2 ∈ criticalSet π then critical π A p.2 else
    regular π A ⟨p.2, hy⟩ (chartAt ℂ (transported A p.1 (π.map p.2)))

theorem rawChart_center (hBranch : range b = branchValues π) (p : Parameters m × Y) :
    p ∈ (rawChart π A p).source := by
  by_cases hy : p.2 ∈ criticalSet π
  · rw [rawChart, dite_eq_left hy]
    exact critical_center π A hBranch hy p.1
  · rw [rawChart, dite_eq_right hy]
    exact regular_center π A ⟨p.2, hy⟩ p.1

theorem rawChart_transition_contDiffAt (i j : Parameters m × Y) (p : Space m × ℂ)
    (hp : p ∈ ((rawChart π A i).symm.trans (rawChart π A j)).source) :
    ContDiffAt ℂ ω ((rawChart π A i).symm.trans (rawChart π A j)) p := by
  by_cases hi : i.2 ∈ criticalSet π
  · rw [rawChart, dite_eq_left hi] at hp ⊢
    by_cases hj : j.2 ∈ criticalSet π
    · rw [rawChart, dite_eq_left hj] at hp ⊢
      exact critical_critical π A i.2 j.2 p hp
    · rw [rawChart, dite_eq_right hj] at hp ⊢
      exact critical_regular π A i.2 ⟨j.2, hj⟩ _ (mdifferentiable_chart _) p hp
  · rw [rawChart, dite_eq_right hi] at hp ⊢
    by_cases hj : j.2 ∈ criticalSet π
    · rw [rawChart, dite_eq_left hj] at hp ⊢
      exact regular_critical π A ⟨i.2, hi⟩ _ (mdifferentiable_chart _) j.2 p hp
    · rw [rawChart, dite_eq_right hj] at hp ⊢
      exact regular_regular π A ⟨i.2, hi⟩ ⟨j.2, hj⟩ _ _ (mdifferentiable_chart _) (mdifferentiable_chart _) p hp

theorem rawChart_transition_contDiffOn (i j : Parameters m × Y) :
    ContDiffOn ℂ ω ((rawChart π A i).symm.trans (rawChart π A j))
      ((rawChart π A i).symm.trans (rawChart π A j)).source :=
  fun p hp => (rawChart_transition_contDiffAt π A i j p hp).contDiffWithinAt

theorem rawChart_parameter (p q : Parameters m × Y) : (rawChart π A p q).1 = q.1.val := by
  by_cases hy : p.2 ∈ criticalSet π
  · rw [rawChart, dite_eq_left hy]
    rfl
  · rw [rawChart, dite_eq_right hy, regular_apply]

end VeechDichotomy.NativeAnalyticCoverTransitions
