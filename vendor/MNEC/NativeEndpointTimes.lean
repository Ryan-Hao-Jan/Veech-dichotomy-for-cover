module

public import MNEC.NativeCompactDirectionalContinuation
public import Mathlib.Topology.Connected.Clopen

/-! Actual finite boundary times and countable rational tail observations
for the maximal native domain of an arbitrary original differential.
Openness/nonempty native domain and connected real time give an excluded
boundary point whenever the orbit is incomplete. Every eventual original
neighborhood condition has an open convex native tail with the SAME
endpoint filter and an actual rational time in that tail. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeEndpointTimes

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativeDirectionalDynamics Set Filter Topology
open scoped Classical Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem exists_excluded_boundary (q : Differential X) (v : Plane) (x : Regular q)
    (hproper : domain q v x ≠ univ) :
    ∃ B : ℝ, B ∈ closure (domain q v x) ∧ B ∉ domain q v x := by
  obtain ⟨B, hB⟩ := nonempty_frontier_iff.mpr
    (show (domain q v x).Nonempty ∧ domain q v x ≠ univ from ⟨⟨0, zero_mem_domain q v x⟩, hproper⟩)
  change B ∈ closure (domain q v x) \ interior (domain q v x) at hB
  rw [(domain_open q v x).interior_eq] at hB
  exact ⟨B, hB⟩

theorem exists_rational_mem_open {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty) :
    ∃ a : ℚ, (a : ℝ) ∈ I := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI t ht
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show t - δ < t + δ by linarith)
  refine ⟨a, hball ?_⟩
  rw [Real.ball_eq_Ioo]
  exact ⟨ha₁, ha₂⟩

theorem rational_tail (q : Differential X) (v : Plane) (x : Regular q) (B : ℝ)
    (hB : B ∈ closure (domain q v x)) (U : Set X)
    (hstay : ∀ᶠ t in 𝓝[domain q v x] B, (trajectory q v x t).val ∈ U) :
    ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ I ⊆ domain q v x ∧
      𝓝[I] B = 𝓝[domain q v x] B ∧
        (∀ t ∈ I, (trajectory q v x t).val ∈ U) ∧ ∃ a : ℚ, (a : ℝ) ∈ I := by
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hstay
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let I := domain q v x ∩ Metric.ball B ε
  have hI : IsOpen I := (domain_open q v x).inter Metric.isOpen_ball
  have hconvex : Convex ℝ I := (domain_convex q v x).inter (convex_ball B ε)
  have hfilter : 𝓝[I] B = 𝓝[domain q v x] B := by
    change 𝓝[domain q v x ∩ Metric.ball B ε] B = 𝓝[domain q v x] B
    rw [inter_comm]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds B hε))
  let : NeBot (𝓝[domain q v x] B) := mem_closure_iff_nhdsWithin_neBot.mp hB
  let : NeBot (𝓝[I] B) := by rw [hfilter]; infer_instance
  have hne : I.Nonempty := by
    have hmem : ∀ᶠ t in 𝓝[I] B, t ∈ I := self_mem_nhdsWithin
    obtain ⟨t, ht⟩ := Filter.Eventually.exists hmem
    exact ⟨t, ht⟩
  refine ⟨I, hI, hconvex, inter_subset_left, hfilter, ?_, exists_rational_mem_open hI hne⟩
  intro t ht
  exact hsub ⟨hball ht.2, ht.1⟩

end MNEC.NativeEndpointTimes

