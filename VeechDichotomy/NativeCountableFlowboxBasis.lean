module

public import VeechDichotomy.NativeFlowboxNeighborhoods

/-! A countable family of concrete buffered primitive boxes forms a
basis of the actual regular surface. Its complete-phase preimages form
a basis of the actual native flow phase space. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCountableFlowboxBasis

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativePrimitiveRectangles NativeBufferedFlowboxes
open NativeFlowboxNeighborhoods Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem regular_basis : IsTopologicalBasis (range (Data.region (q := q))) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨D, rfl⟩
    exact D.region_open
  · intro x U hx hU
    obtain ⟨D, hxD, hDU⟩ := exists_box q x hU hx
    exact ⟨D.region, mem_range_self D, hxD, hDU⟩

theorem exists_countable_basis :
    ∃ D : ℕ → Data q, IsTopologicalBasis (range (fun j => (D j).region)) := by
  classical
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  obtain ⟨s, hs, hcount, hb⟩ := (regular_basis q).exists_countable
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := regular_nonempty q
    obtain ⟨U, hUs, _, _⟩ := hb.exists_subset_of_mem_open (mem_univ x) isOpen_univ
    exact ⟨U, hUs⟩
  obtain ⟨f, hf⟩ := hcount.exists_eq_range hsne
  have hex : ∀ j, ∃ D : Data q, D.region = f j := by
    intro j
    apply hs
    rw [hf]
    exact mem_range_self j
  choose D hD using hex
  refine ⟨D, ?_⟩
  have heq : (fun j => (D j).region) = f := funext hD
  rw [heq, ← hf]
  exact hb

theorem phase_basis (D : ℕ → Data q) (hD : IsTopologicalBasis (range (fun j => (D j).region))) :
    IsTopologicalBasis (range (fun j => (D j).phaseRegion)) := by
  have hb : IsTopologicalBasis ((fun U : Set (Regular q) =>
      (Subtype.val : CompleteOrbits q vertical → Regular q) ⁻¹' U) ''
      range (fun j => (D j).region)) :=
    Topology.IsInducing.subtypeVal.isTopologicalBasis hD
  have heq : (fun U : Set (Regular q) =>
      (Subtype.val : CompleteOrbits q vertical → Regular q) ⁻¹' U) ''
      range (fun j => (D j).region) = range (fun j => (D j).phaseRegion) := by
    ext V
    constructor
    · rintro ⟨U, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(D j).region, mem_range_self j, rfl⟩
  rw [heq] at hb
  exact hb

end VeechDichotomy.NativeCountableFlowboxBasis
