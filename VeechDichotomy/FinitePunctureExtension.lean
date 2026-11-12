module

public import VeechDichotomy.FinitePunctureNeighborhoods
public import VeechDichotomy.ConnectedEndLimit

/-! Continuous extensions across finite punctures of complex curves.
The continuous map to a compact target is extended from its derived
unique limits, when its finite-fiber projection already extends. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FinitePunctureExtension

open Set Filter Topology FinitePunctureNeighborhoods

variable {Y F X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace F] [CompactSpace F] [T2Space F]
  [TopologicalSpace X] [T2Space X]

theorem outside_dense {S : Set Y} (hS : S.Finite) : Dense (outside S) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨a, ha⟩ := hUne
  obtain ⟨t, _, htsub, htconn⟩ := connected_basis hS a
    ((Subtype.val : outside S → Y) ⁻¹' U) (Filter.preimage_mem_comap (hU.mem_nhds ha))
  obtain ⟨y, hy⟩ := htconn.nonempty
  exact ⟨y.val, htsub hy, y.property⟩

theorem exists_extension {S : Set Y} (hS : S.Finite) (f : outside S → F)
    (hf : Continuous f) (q : F → X) (hq : Continuous q)
    (hfinite : ∀ x, (q ⁻¹' {x}).Finite) (P : Y → X) (hP : Continuous P)
    (hsquare : ∀ y : outside S, q (f y) = P y.val) :
    ∃ H : C(Y, F), (∀ y : outside S, H y.val = f y) ∧ q ∘ H = P := by
  have hd : Dense (outside S) := outside_dense hS
  have hlimits : ∀ a : Y, ∃ b : F,
      Tendsto f (Filter.comap (Subtype.val : outside S → Y) (𝓝 a)) (𝓝 b) := by
    intro a
    let l := Filter.comap (Subtype.val : outside S → Y) (𝓝 a)
    have : NeBot l := hd.comap_val_nhds_neBot a
    apply ConnectedEndLimit.exists_limit f q hq (P a) (hfinite (P a))
    · have heq : q ∘ f = P ∘ (Subtype.val : outside S → Y) := funext hsquare
      rw [heq]
      exact hP.continuousAt.tendsto.comp (show Tendsto (Subtype.val : outside S → Y) l (𝓝 a) from Filter.map_comap_le)
    · intro s hs
      obtain ⟨t, ht, htsub, htconn⟩ := connected_basis hS a s hs
      exact ⟨t, ht, htsub, htconn.isPreconnected.image f hf.continuousOn⟩
  let H : C(Y, F) := ⟨hd.extend f, hd.continuous_extend hlimits⟩
  have hvalue : ∀ y : outside S, H y.val = f y := hd.extend_eq hf
  refine ⟨H, hvalue, ?_⟩
  apply Continuous.ext_on hd (hq.comp H.continuous) hP
  intro y hy
  change q (H y) = P y
  rw [hvalue ⟨y, hy⟩]
  exact hsquare ⟨y, hy⟩

end VeechDichotomy.FinitePunctureExtension
