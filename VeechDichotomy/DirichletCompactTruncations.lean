module

public import VeechDichotomy.DirichletKleinClosure

/-! Removing any open Klein neighborhoods of all actual ideal endpoints
leaves a genuinely compact subset of the actual upper half-plane.
This is a compact truncation statement; no parabolic or cusp-neighborhood
classification is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCompactTruncations

open LinearGroup Set HyperbolicDirichletRegions HyperbolicKleinMap HyperbolicKleinHomeomorph
open DirichletKleinClosure DirichletIdealRadialPoints
open scoped UpperHalfPlane

def truncation (Γ : Subgroup SL2) (p : ℍ) (U : Set ℂ) : Set ℍ :=
  {z | z ∈ region Γ p ∧ point z ∉ U}

theorem point_isEmbedding : Topology.IsEmbedding point := by
  change Topology.IsEmbedding ((Subtype.val : Disk → ℂ) ∘ homeomorph)
  exact Topology.IsEmbedding.subtypeVal.comp homeomorph.isEmbedding

theorem image_truncation (Γ : Subgroup SL2) (p : ℍ) (U : Set ℂ) (hU : idealBoundary Γ p ⊆ U) :
    point '' truncation Γ p U = closedRegion Γ p \ U := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨subset_closure ⟨z, hz.1, rfl⟩, hz.2⟩
  · intro u hu
    rcases mem_or_ideal Γ p hu.1 with ⟨z, hz, rfl⟩ | hi
    · exact ⟨z, ⟨hz, hu.2⟩, rfl⟩
    · exact False.elim (hu.2 (hU hi))

theorem isCompact_truncation (Γ : Subgroup SL2) (p : ℍ) (U : Set ℂ) (hopen : IsOpen U)
    (hU : idealBoundary Γ p ⊆ U) : IsCompact (truncation Γ p U) := by
  apply point_isEmbedding.isCompact_iff.mpr
  rw [image_truncation Γ p U hU]
  exact (isCompact_closedRegion Γ p).inter_right hopen.isClosed_compl

def idealNeighborhoods (Γ : Subgroup SL2) (p : ℍ) (ε : ℝ) : Set ℂ :=
  ⋃ u ∈ idealBoundary Γ p, Metric.ball u ε

theorem idealNeighborhoods_open (Γ : Subgroup SL2) (p : ℍ) (ε : ℝ) :
    IsOpen (idealNeighborhoods Γ p ε) := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball))

theorem ideal_subset_neighborhoods (Γ : Subgroup SL2) (p : ℍ) (ε : ℝ) (hε : 0 < ε) :
    idealBoundary Γ p ⊆ idealNeighborhoods Γ p ε := by
  intro u hu
  exact mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hu, Metric.mem_ball_self hε⟩⟩

theorem isCompact_outside_ideal_balls (Γ : Subgroup SL2) (p : ℍ) (ε : ℝ) (hε : 0 < ε) :
    IsCompact (truncation Γ p (idealNeighborhoods Γ p ε)) :=
  isCompact_truncation Γ p _ (idealNeighborhoods_open Γ p ε) (ideal_subset_neighborhoods Γ p ε hε)

end VeechDichotomy.DirichletCompactTruncations
