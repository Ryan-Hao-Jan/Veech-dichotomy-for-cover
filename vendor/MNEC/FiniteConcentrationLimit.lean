module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.ClusterPt
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex

/-! A continuous curve on a real interval that eventually enters every
open neighborhood of a finite set has an actual single-point limit at any
boundary time. Compactness supplies a cluster point; connected small time
tails prevent switching between separated finite-set neighborhoods. -/

@[expose] public section
noncomputable section
namespace MNEC.FiniteConcentrationLimit

open Set Filter Topology Metric
open scoped Classical

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Pure topology. No selected limiting point or convergence hypothesis is
assumed; finite-set concentration and connected time tails derive it. -/
theorem exists_limit (D : Set ℝ) (hD : Convex ℝ D) (B : ℝ) (hB : B ∈ closure D)
    (γ : ℝ → X) (hγ : ContinuousOn γ D) (Z : Set X) (hZ : Z.Finite)
    (hnear : ∀ U : Set X, IsOpen U → Z ⊆ U → ∀ᶠ t in 𝓝[D] B, γ t ∈ U) :
    ∃ z ∈ Z, Tendsto γ (𝓝[D] B) (𝓝 z) := by
  let F := 𝓝[D] B
  let : NeBot F := mem_closure_iff_nhdsWithin_neBot.mp hB
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (Filter.map γ F)
  have hzZ : z ∈ Z := by
    by_contra hnot
    obtain ⟨V, hV, hzV, hcl⟩ := normal_exists_closure_subset
      (isClosed_singleton : IsClosed ({z} : Set X)) hZ.isClosed.isOpen_compl
      (singleton_subset_iff.mpr hnot)
    have hZW : Z ⊆ (closure V)ᶜ := by
      intro y hy hycl
      exact hcl hycl hy
    have hW : (closure V)ᶜ ∈ Filter.map γ F :=
      hnear _ isClosed_closure.isOpen_compl hZW
    obtain ⟨y, hyV, hyW⟩ := clusterPt_iff_nonempty.mp hz (hV.mem_nhds (hzV (mem_singleton z))) hW
    exact hyW (subset_closure hyV)
  refine ⟨z, hzZ, tendsto_nhds.mpr ?_⟩
  intro V hV hzV
  let O := V ∩ (Z \ {z})ᶜ
  have hOther : (Z \ {z}).Finite := hZ.subset sdiff_subset
  have hO : IsOpen O := hV.inter hOther.isClosed.isOpen_compl
  have hzO : z ∈ O := ⟨hzV, by rintro ⟨_, hne⟩; exact hne (mem_singleton z)⟩
  obtain ⟨W, hW, hzW, hclW⟩ := normal_exists_closure_subset
    (isClosed_singleton : IsClosed ({z} : Set X)) hO (singleton_subset_iff.mpr hzO)
  let N := (closure W)ᶜ
  have hN : IsOpen N := isClosed_closure.isOpen_compl
  have hDisj : Disjoint W N := disjoint_left.mpr (fun _ hw hn => hn (subset_closure hw))
  have hZWN : Z ⊆ W ∪ N := by
    intro y hy
    by_cases hyz : y = z
    · exact Or.inl (hyz ▸ hzW (mem_singleton z))
    · apply Or.inr
      intro hycl
      exact (hclW hycl).2 ⟨hy, fun heq => hyz (mem_singleton_iff.mp heq)⟩
  have hWN := hnear (W ∪ N) (hW.union hN) hZWN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hWN
  let T := Metric.ball B ε ∩ D
  have hT : T ∈ F := Metric.mem_nhdsWithin_iff.mpr ⟨ε, hε, subset_rfl⟩
  have hIm : γ '' T ∈ Filter.map γ F := by
    change γ ⁻¹' (γ '' T) ∈ F
    exact Filter.mem_of_superset hT (fun t ht => ⟨t, ht, rfl⟩)
  obtain ⟨y, hyW, hyIm⟩ := clusterPt_iff_nonempty.mp hz (hW.mem_nhds (hzW (mem_singleton z))) hIm
  have hConnected : IsPreconnected (γ '' T) :=
    ((convex_ball B ε).inter hD).isPreconnected.image γ (hγ.mono inter_subset_right)
  have hSub : γ '' T ⊆ W ∪ N := by
    rintro _ ⟨t, ht, rfl⟩
    exact hball ht
  have hAll : γ '' T ⊆ W := hConnected.subset_left_of_subset_union hW hN hDisj hSub ⟨y, hyIm, hyW⟩
  have hWV : W ⊆ V := (subset_closure.trans hclW).trans inter_subset_left
  exact Filter.mem_of_superset hT (fun t ht => hWV (hAll ⟨t, ht, rfl⟩))

end MNEC.FiniteConcentrationLimit
