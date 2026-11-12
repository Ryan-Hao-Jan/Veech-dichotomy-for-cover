module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Compactness.LocallyCompact

/-! Compact representatives above compact subsets of an open quotient.
This proves the compact-lift step of the paper without any assumption that
the quotient map itself is proper, or that the subgroup is normal.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

theorem exists_compact_lift_of_open_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace X] {f : X → Y}
    (hf : IsOpenMap f) (hs : Function.Surjective f)
    {C : Set Y} (hC : IsCompact C) :
    ∃ K : Set X, IsCompact K ∧ C ⊆ f '' K := by
  classical
  choose K hK hKx using fun x : X => exists_compact_mem_nhds x
  have hcover : C ⊆ ⋃ x : X, f '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    exact mem_iUnion.mpr ⟨x, mem_image_of_mem f (mem_interior_iff_mem_nhds.mpr (hKx x))⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun x : X => f '' interior (K x)) (fun _ => hf _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion (fun x _ => hK x), ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp (ht hy)
  obtain ⟨hxt, z, hz, rfl⟩ := mem_iUnion.mp hx
  exact ⟨z, mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxt, interior_subset hz⟩⟩, rfl⟩

/-- A compact set in `G/Γ` has representatives in a compact subset of `G`.
The quotient uses cosets `gΓ`, as in the manuscript. -/
theorem exists_compact_quotient_lift
    {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (Γ : Subgroup G) {C : Set (G ⧸ Γ)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ QuotientGroup.mk '' K :=
  exists_compact_lift_of_open_surjective QuotientGroup.isOpenMap_coe
    QuotientGroup.mk_surjective hC

/-- In the normalization `A = Hγ`, the correction multiplies on the right. -/
theorem exists_compact_right_normalizers
    {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (Γ : Subgroup G) {C : Set (G ⧸ Γ)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ ∀ H : G,
      (QuotientGroup.mk H : G ⧸ Γ) ∈ C → ∃ γ : Γ, H * γ ∈ K := by
  obtain ⟨K, hK, hCK⟩ := exists_compact_quotient_lift Γ hC
  refine ⟨K, hK, ?_⟩
  intro H hH
  obtain ⟨A, hAK, hAH⟩ := hCK hH
  have hγ : H⁻¹ * A ∈ Γ := QuotientGroup.eq.mp hAH.symm
  refine ⟨⟨H⁻¹ * A, hγ⟩, ?_⟩
  simpa only [mul_inv_cancel_left] using hAK

end VeechDichotomy
