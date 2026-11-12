module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Compactness.Compact

/-! A map with connected images of arbitrarily small filter neighborhoods
has a limit in a compact target if its composition with a continuous
finite-fiber map converges. Distinct possible limits would separate one
such connected image into two nonempty open pieces. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ConnectedEndLimit

open Set Filter Topology

variable {D F X : Type*} [TopologicalSpace F] [CompactSpace F] [T2Space F]
  [TopologicalSpace X] [T2Space X]

theorem exists_limit {l : Filter D} [NeBot l] (f : D → F) (q : F → X)
    (hq : Continuous q) (x : X) (hfinite : (q ⁻¹' {x}).Finite)
    (ht : Tendsto (q ∘ f) l (𝓝 x))
    (hconnected : ∀ s ∈ l, ∃ t ∈ l, t ⊆ s ∧ IsPreconnected (f '' t)) :
    ∃ z : F, Tendsto f l (𝓝 z) := by
  have in_fiber : ∀ z, MapClusterPt z l f → q z = x := by
    intro z hz
    have hc := hz.continuousAt_comp hq.continuousAt
    exact eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (Filter.map f l)
  refine ⟨z, tendsto_nhds_of_unique_mapClusterPt ?_⟩
  intro w hw
  by_contra hne
  have hzF : z ∈ q ⁻¹' {x} := in_fiber z hz
  have hwF : w ∈ q ⁻¹' {x} := in_fiber w hw
  have hrest : IsClosed ((q ⁻¹' {x}) \ {z}) := hfinite.sdiff.isClosed
  obtain ⟨U, V, hU, hV, hzU, hrestV, hUV⟩ :=
    normal_separation (isClosed_singleton (x := z)) hrest (by
      rw [disjoint_singleton_left]
      exact fun h => h.2 rfl)
  have hzU' : z ∈ U := hzU (mem_singleton z)
  have hwV : w ∈ V := hrestV ⟨hwF, hne⟩
  have hfiberUV : q ⁻¹' {x} ⊆ U ∪ V := by
    intro y hy
    by_cases hyz : y = z
    · exact Or.inl (hyz ▸ hzU')
    · exact Or.inr (hrestV ⟨hy, hyz⟩)
  let C : Set F := (U ∪ V)ᶜ
  have hqC : IsClosed (q '' C) := (((hU.union hV).isClosed_compl).isCompact.image hq).isClosed
  have hxC : x ∉ q '' C := by
    rintro ⟨y, hyC, hxy⟩
    exact hyC (hfiberUV hxy)
  have hnear : f ⁻¹' (U ∪ V) ∈ l := by
    filter_upwards [ht (hqC.isOpen_compl.mem_nhds hxC)] with y hy
    by_contra hyUV
    exact hy ⟨f y, hyUV, rfl⟩
  obtain ⟨t, htmem, htsub, htconn⟩ := hconnected (f ⁻¹' (U ∪ V)) hnear
  have htimage : f '' t ∈ Filter.map f l := Filter.image_mem_map htmem
  have hhitU : (f '' t ∩ U).Nonempty := by
    obtain ⟨u, huU, hut⟩ := (clusterPt_iff_nonempty.mp hz) (hU.mem_nhds hzU') htimage
    exact ⟨u, hut, huU⟩
  have hhitV : (f '' t ∩ V).Nonempty := by
    obtain ⟨u, huV, hut⟩ := (clusterPt_iff_nonempty.mp hw) (hV.mem_nhds hwV) htimage
    exact ⟨u, hut, huV⟩
  have hsubset : f '' t ⊆ U ∪ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact htsub hy
  obtain ⟨u, _, huU, huV⟩ := htconn U V hU hV hsubset hhitU hhitV
  exact disjoint_left.mp hUV huU huV

end VeechDichotomy.ConnectedEndLimit
