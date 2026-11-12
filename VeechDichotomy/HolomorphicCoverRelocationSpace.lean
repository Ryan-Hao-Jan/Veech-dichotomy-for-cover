module

public import VeechDichotomy.HolomorphicCoverRelocationTransitions

/-! A constructed complex structure on the original covering-source
topology after relocation. The actual transported covering map is
holomorphic in this structure, in every complex dimension. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCoverRelocationSpace

open Set Filter Topology HolomorphicCoverRelocationData HolomorphicCoverRelocationTransitions
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E N]

structure Source (A : Data (E := E) (M := M) (N := N)) where
  point : M

variable (A : Data (E := E) (M := M) (N := N))

instance topology : TopologicalSpace (Source A) := TopologicalSpace.induced Source.point inferInstance

def toOriginal : Source A ≃ₜ M where
  toFun := Source.point
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space [T2Space M] : T2Space (Source A) := (toOriginal A).isEmbedding.t2Space

def chart (x : Source A) : OpenPartialHomeomorph (Source A) E :=
  (toOriginal A).transOpenPartialHomeomorph (rawChart A x.point)

theorem chart_center (x : Source A) : x ∈ (chart A x).source := rawChart_center A x.point

@[instance_reducible] def chartedSpace : ChartedSpace E (Source A) where
  atlas := range (chart A)
  chartAt := chart A
  mem_chart_source := chart_center A
  chart_mem_atlas x := ⟨x, rfl⟩

variable [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, E) ω N]

theorem transition_holomorphicOn (i j : Source A) :
    ContDiffOn ℂ ω ((chart A i).symm.trans (chart A j)) ((chart A i).symm.trans (chart A j)).source := by
  change ContDiffOn ℂ ω ((rawChart A i.point).symm.trans (rawChart A j.point))
    ((rawChart A i.point).symm.trans (rawChart A j.point)).source
  exact rawChart_transitionOn A i.point j.point

theorem isComplexManifold : letI := chartedSpace A
    IsManifold 𝓘(ℂ, E) ω (Source A) := by
  let := chartedSpace A
  let : HasGroupoid (Source A) (contDiffGroupoid ω 𝓘(ℂ, E)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ, E))
    intro e f he hf
    change e ∈ range (chart A) at he
    change f ∈ range (chart A) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_holomorphicOn A i j
  exact IsManifold.mk' 𝓘(ℂ, E) ω (Source A)

attribute [instance] chartedSpace isComplexManifold

def map (x : Source A) : N := A.transport (A.map x.point)

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, E) ω N] in
theorem continuous_map : Continuous (map A) :=
  A.transport.continuous.comp (A.holomorphic.continuous.comp (toOriginal A).continuous)

theorem toOriginal_holomorphicAt_critical (x : Source A) (hx : x.point ∈ A.critical) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (toOriginal A) x := by
  have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chart A x) x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) (chart_center A x)
  have hraw : rawChart A x.point = A.criticalChart x.point := by rw [rawChart, dite_eq_left hx]
  have ht : chart A x x ∈ (A.criticalChart x.point).target := by
    rw [← hraw]
    exact (rawChart A x.point).map_source (rawChart_center A x.point)
  have hi := critical_inverse A x.point ht
  apply (hi.comp x hc).congr_of_eventuallyEq
  filter_upwards [(chart A x).open_source.mem_nhds (chart_center A x)] with y hy
  change y.point = (A.criticalChart x.point).symm (rawChart A x.point y.point)
  rw [hraw]
  exact ((A.criticalChart x.point).left_inv (hraw ▸ hy)).symm

theorem holomorphic_map : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (map A) := by
  intro x
  by_cases hx : x.point ∈ A.critical
  · exact (A.transport_holomorphic _ (A.critical_region x.point hx)).comp x
      ((A.holomorphic x.point).comp x (toOriginal_holomorphicAt_critical A x hx))
  · let i : ↥(A.criticalᶜ) := ⟨x.point, hx⟩
    have hraw : rawChart A x.point = A.regularChart i := by rw [rawChart, dite_eq_right hx]
    have hsrc : x.point ∈ (A.regularChart i).source := hraw ▸ rawChart_center A x.point
    have ht : chart A x x ∈ (A.targetChart i).target := by
      change rawChart A x.point x.point ∈ _
      rw [hraw, A.regular_apply]
      exact (A.targetChart i).map_source ((A.regular_source i x.point).mp hsrc).2
    have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (A.targetChart i).symm (chart A x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (A.transport (A.map i.val))) ht
    have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chart A x) x :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) (chart_center A x)
    apply (hi.comp x hc).congr_of_eventuallyEq
    filter_upwards [(chart A x).open_source.mem_nhds (chart_center A x)] with y hy
    change A.transport (A.map y.point) = (A.targetChart i).symm (rawChart A x.point y.point)
    rw [hraw, A.regular_apply]
    exact ((A.targetChart i).left_inv ((A.regular_source i y.point).mp (hraw ▸ hy)).2).symm

end VeechDichotomy.HolomorphicCoverRelocationSpace
