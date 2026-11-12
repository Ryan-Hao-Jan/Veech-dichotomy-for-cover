module

public import VeechDichotomy.FinitePunctureHomotopy
public import Mathlib.Topology.Homotopy.Path

/-! A finite-punctured compact complex curve has a constructed compact
core carrying all based loop classes. Disjoint radial chart homotopies
move its points outside fixed puncture disks and keep the basepoint fixed.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PuncturedCompactCore

open Set Topology unitInterval FinitePunctureNeighborhoods FinitePunctureHomotopy

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]

theorem exists_core {S : Set X} (hS : S.Finite) (o : outside S) :
    ∃ K : Set (outside S), IsCompact K ∧ o ∈ K ∧
      ∃ f : C(outside S, outside S), ∃ H : (ContinuousMap.id (outside S)).Homotopy f,
        (∀ t, H (t, o) = o) ∧ range f ⊆ K := by
  classical
  obtain ⟨D, hD, hdisj⟩ := PunctureDisks.exists_disjoint_family hS o.property
  let : Finite S := hS.to_subtype
  let := Fintype.ofFinite S
  obtain ⟨f, H, hHfix, havoid⟩ := exists_push D hdisj o (fun a => (hD a).2.2) Finset.univ
  let L : Set X := (⋃ a : S, inner (D a))ᶜ
  have hLclosed : IsClosed L := (isOpen_iUnion fun a => inner_open (D a)).isClosed_compl
  have hLout : L ⊆ outside S := by
    intro x hx hxS
    have hxInner : x ∈ inner (D ⟨x, hxS⟩) := by
      simpa only [(hD ⟨x, hxS⟩).1] using center_mem_inner (D ⟨x, hxS⟩) (hD ⟨x, hxS⟩).2.1
    exact hx (mem_iUnion.mpr ⟨⟨x, hxS⟩, hxInner⟩)
  have hoL : o.val ∈ L := by
    intro hoUnion
    obtain ⟨a, ha⟩ := mem_iUnion.mp hoUnion
    exact (hD a).2.2 (inner_subset_support _ ha)
  let K : Set (outside S) := Subtype.val ⁻¹' L
  have hK : IsCompact K := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    have himage : (Subtype.val : outside S → X) '' K = L := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hLout hx⟩, hx, rfl⟩
    rw [himage]
    exact hLclosed.isCompact
  refine ⟨K, hK, hoL, f, H, hHfix, ?_⟩
  rintro _ ⟨x, rfl⟩
  intro hUnion
  obtain ⟨a, ha⟩ := mem_iUnion.mp hUnion
  exact havoid a (Finset.mem_univ a) x ha

end VeechDichotomy.PuncturedCompactCore

namespace VeechDichotomy.BasedHomotopyLoops

open Set unitInterval

variable {Y : Type*} [TopologicalSpace Y] {f : C(Y, Y)}

theorem exists_image_loop (H : (ContinuousMap.id Y).Homotopy f) (o : Y)
    (hfix : ∀ t, H (t, o) = o) (γ : Path o o) :
    ∃ η : Path o o, range η ⊆ range f ∧ γ.Homotopic η := by
  have hfo : f o = o := by rw [← H.apply_one o]; exact hfix 1
  let η : Path o o := (γ.map f.continuous).cast hfo.symm hfo.symm
  have hη : range η ⊆ range f := by
    rintro _ ⟨u, rfl⟩
    exact ⟨γ u, rfl⟩
  refine ⟨η, hη, ⟨?_⟩⟩
  refine
    { toContinuousMap := ⟨fun p => H (p.1, γ p.2),
        H.continuous.comp (continuous_fst.prodMk (γ.continuous.comp continuous_snd))⟩
      map_zero_left := fun u => H.apply_zero (γ u)
      map_one_left := fun u => H.apply_one (γ u)
      prop' := ?_ }
  intro t u hu
  change H (t, γ u) = γ u
  rcases hu with h0 | h1
  · rw [h0, γ.source]
    exact hfix t
  · have h1' : u = 1 := h1
    rw [h1', γ.target]
    exact hfix t

end VeechDichotomy.BasedHomotopyLoops
