module

public import VeechDichotomy.DirichletKleinClosure
public import Mathlib.Analysis.Convex.Extreme

/-! Every extreme point in the open-disk part of the actual Dirichlet
closure is an actual true corner. At a noncorner the actual local cone
contains a line; genuine region points in its two opposite directions
put the point in the interior of a nontrivial actual segment. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletExtremePoints

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicKleinMap
open DirichletKleinClosure DirichletIdealRadialPoints
open scoped UpperHalfPlane

theorem opposite_segment (x u : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    x ∈ openSegment ℝ (x + t • u) (x + s • (-u)) := by
  have hd : 0 < t + s := add_pos ht hs
  have hsum : s / (t + s) + t / (t + s) = 1 := by field_simp; ring
  have hcancel : (s / (t + s)) * t - (t / (t + s)) * s = 0 := by ring
  refine ⟨s / (t + s), t / (t + s), div_pos hs hd, div_pos ht hd, hsum, ?_⟩
  calc
    _ = (s / (t + s) + t / (t + s)) • x +
        ((s / (t + s)) * t - (t / (t + s)) * s) • u := by module
    _ = x := by rw [hsum, hcancel, one_smul, zero_smul, add_zero]

theorem noncorner_not_extreme (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ)
    (hz : z ∈ region Γ p) (hn : z ∉ corners Γ p) :
    point z ∉ (closedRegion Γ p).extremePoints ℝ := by
  obtain ⟨u, hune, hu, hneg⟩ := DirichletNoncornerWidth.noncorner_has_line Γ p z hz hn
  obtain ⟨t, w, ht, hw, _, hwpoint⟩ := DirichletConeDirections.ray_realized Γ p z hz hu hune
  obtain ⟨s, v, hs, hv, _, hvpoint⟩ :=
    DirichletConeDirections.ray_realized Γ p z hz hneg (neg_ne_zero.mpr hune)
  have hw' : point w = point z + t • u := by rw [← hwpoint]; abel
  have hv' : point v = point z + s • (-u) := by rw [← hvpoint]; abel
  have hseg : point z ∈ openSegment ℝ (point w) (point v) := by
    rw [hw', hv']
    exact opposite_segment _ _ s t hs ht
  intro he
  have heq := (mem_extremePoints_iff_left.mp he).2 (point w) (subset_closure ⟨w, hw, rfl⟩)
    (point v) (subset_closure ⟨v, hv, rfl⟩) hseg
  rw [heq, sub_self] at hwpoint
  exact smul_ne_zero ht.ne' hune hwpoint.symm

def vertices (Γ : Subgroup SL2) (p : ℍ) : Set ℂ := point '' corners Γ p ∪ idealBoundary Γ p

theorem vertices_subset (Γ : Subgroup SL2) (p : ℍ) : vertices Γ p ⊆ closedRegion Γ p := by
  rintro u (⟨z, hz, rfl⟩ | hu)
  · exact subset_closure ⟨z, hz.1, rfl⟩
  · exact hu.1

theorem extremePoints_subset_vertices (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) :
    (closedRegion Γ p).extremePoints ℝ ⊆ vertices Γ p := by
  intro u hu
  rcases mem_or_ideal Γ p hu.1 with ⟨z, hz, rfl⟩ | hi
  · apply Or.inl
    refine ⟨z, ?_, rfl⟩
    by_contra hn
    exact noncorner_not_extreme Γ p z hz hn hu
  · exact Or.inr hi

end VeechDichotomy.DirichletExtremePoints
