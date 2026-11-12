module

public import VeechDichotomy.HolomorphicCoverRelocationData

/-! All four analytic transition cases for source relocation in any
complex dimension. Regular/regular transitions cancel the actual transport;
mixed transitions use its proved analytic germs only in the marked region. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCoverRelocationTransitions

open Set Filter Topology HolomorphicCoverRelocationData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) ω N]
variable (A : Data (E := E) (M := M) (N := N))

omit [IsManifold 𝓘(ℂ, E) ω N] in
theorem critical_forward (i : M) {x : M} (hx : x ∈ (A.criticalChart i).source) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.criticalChart i) x := by
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E i) x
  exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas i) hx.1

omit [IsManifold 𝓘(ℂ, E) ω N] in
theorem critical_inverse (i : M) {z : E} (hz : z ∈ (A.criticalChart i).target) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.criticalChart i).symm z := by
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E i).symm z
  exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas i) hz.1

omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem regular_forward (i : ↥(A.criticalᶜ)) {x : M} (hx : x ∈ (A.regularChart i).source)
    (hregion : A.map x ∈ A.region) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.regularChart i) x := by
  have ht := (A.regular_source i x).mp hx
  have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.targetChart i) (A.transport (A.map x)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (A.transport (A.map i.val))) ht.2
  apply (hc.comp x ((A.transport_holomorphic _ hregion).comp x (A.holomorphic x))).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (A.regular_apply i)

omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem regular_inverse (i : ↥(A.criticalᶜ)) {z : E} (hz : z ∈ (A.regularChart i).target)
    (hregion : A.map ((A.regularChart i).symm z) ∈ A.region) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.regularChart i).symm z := by
  have ht := (A.regular_target i z).mp hz
  have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.targetChart i).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (A.transport (A.map i.val))) ht.1
  have hψ := A.inverse_holomorphic _ hregion
  rw [A.regular_inverse_projection i hz] at hψ
  have hlocal := A.local_inverse i _ ht.2
  have hinner := hψ.comp z hc
  have hcomp := hlocal.comp z hinner
  exact hcomp

theorem critical_regular (i : M) (j : ↥(A.criticalᶜ)) {z : E}
    (hz : z ∈ ((A.criticalChart i).symm.trans (A.regularChart j)).source) :
    ContDiffAt ℂ ω ((A.criticalChart i).symm.trans (A.regularChart j)) z := by
  have hx := (A.criticalChart i).map_target hz.1
  have hregion' : (A.criticalChart i).symm z ∈ A.sourceRegion := interior_subset hx.2
  have hregion : A.map ((A.criticalChart i).symm z) ∈ A.region := hregion'
  exact ((regular_forward A j hz.2 hregion).comp z (critical_inverse A i hz.1)).contDiffAt

theorem regular_critical (i : ↥(A.criticalᶜ)) (j : M) {z : E}
    (hz : z ∈ ((A.regularChart i).symm.trans (A.criticalChart j)).source) :
    ContDiffAt ℂ ω ((A.regularChart i).symm.trans (A.criticalChart j)) z := by
  have hsource : (A.regularChart i).symm z ∈ (A.criticalChart j).source := hz.2
  have hregion' : (A.regularChart i).symm z ∈ A.sourceRegion := interior_subset hsource.2
  have hregion : A.map ((A.regularChart i).symm z) ∈ A.region := hregion'
  exact ((critical_forward A j hz.2).comp z (regular_inverse A i hz.1 hregion)).contDiffAt

omit [IsManifold 𝓘(ℂ, E) ω N] in
theorem critical_critical (i j : M) {z : E}
    (hz : z ∈ ((A.criticalChart i).symm.trans (A.criticalChart j)).source) :
    ContDiffAt ℂ ω ((A.criticalChart i).symm.trans (A.criticalChart j)) z :=
  ((critical_forward A j hz.2).comp z (critical_inverse A i hz.1)).contDiffAt

omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem regular_regular (i j : ↥(A.criticalᶜ)) {z : E}
    (hz : z ∈ ((A.regularChart i).symm.trans (A.regularChart j)).source) :
    ContDiffAt ℂ ω ((A.regularChart i).symm.trans (A.regularChart j)) z := by
  have ht := (A.regular_target i z).mp hz.1
  have hsource : (A.regularChart i).symm z ∈ (A.regularChart j).source := hz.2
  have hout := ((A.regular_source j ((A.regularChart i).symm z)).mp hsource).2
  rw [A.regular_inverse_projection i hz.1] at hout
  have hci : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.targetChart i).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (A.transport (A.map i.val))) ht.1
  have hcj : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.targetChart j) ((A.targetChart i).symm z) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (A.transport (A.map j.val))) hout
  apply (hcj.comp z hci).contDiffAt.congr_of_eventuallyEq
  filter_upwards [(A.regularChart i).open_target.mem_nhds hz.1] with w hw
  rw [OpenPartialHomeomorph.trans_apply, A.regular_apply, A.regular_inverse_projection i hw]
  rfl

def rawChart (x : M) : OpenPartialHomeomorph M E := by
  classical
  exact if hx : x ∈ A.critical then A.criticalChart x else A.regularChart ⟨x, hx⟩

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, E) ω N] in
theorem rawChart_center (x : M) : x ∈ (rawChart A x).source := by
  by_cases hx : x ∈ A.critical
  · rw [rawChart, dite_eq_left hx]
    exact A.critical_center hx
  · rw [rawChart, dite_eq_right hx]
    exact A.regular_center ⟨x, hx⟩

theorem rawChart_transition (i j : M) {z : E}
    (hz : z ∈ ((rawChart A i).symm.trans (rawChart A j)).source) :
    ContDiffAt ℂ ω ((rawChart A i).symm.trans (rawChart A j)) z := by
  by_cases hi : i ∈ A.critical
  · rw [rawChart, dite_eq_left hi] at hz ⊢
    by_cases hj : j ∈ A.critical
    · rw [rawChart, dite_eq_left hj] at hz ⊢
      exact critical_critical A i j hz
    · rw [rawChart, dite_eq_right hj] at hz ⊢
      exact critical_regular A i ⟨j, hj⟩ hz
  · rw [rawChart, dite_eq_right hi] at hz ⊢
    by_cases hj : j ∈ A.critical
    · rw [rawChart, dite_eq_left hj] at hz ⊢
      exact regular_critical A ⟨i, hi⟩ j hz
    · rw [rawChart, dite_eq_right hj] at hz ⊢
      exact regular_regular A ⟨i, hi⟩ ⟨j, hj⟩ hz

theorem rawChart_transitionOn (i j : M) :
    ContDiffOn ℂ ω ((rawChart A i).symm.trans (rawChart A j)) ((rawChart A i).symm.trans (rawChart A j)).source :=
  fun _ hz => (rawChart_transition A i j hz).contDiffWithinAt

end VeechDichotomy.HolomorphicCoverRelocationTransitions
