module

public import VeechDichotomy.HyperbolicMetricSegments

/-! Actual metric segments equal the entire ranges of the constructed
constant-speed geodesic paths. A real interval has all affine clocks,
and the proved vertical metric-betweenness characterization proves both
inclusions. Thus every metric-between point, not only a chosen path,
belongs to any actual Dirichlet region containing the endpoints. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicCanonicalSegments

open LinearGroup HyperbolicMetricSegments HyperbolicGeodesicLines HyperbolicCommonGeodesic
open HyperbolicDirichletRegions Set
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

theorem normalized_between_iff (A : SL2) (c s t : ℝ) (z : ℍ) :
    z ∈ metricSegment (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) ↔
      (A • z).re = c ∧ Real.log (A • z).im ∈ uIcc s t := by
  have h₀ := HyperbolicDirichletGeodesics.dist_to_point A c s z
  have h₁ : dist z (HyperbolicDirichletGeodesics.line A c t) = dist (A • z) (verticalPoint c t) := by
    calc
      dist z (HyperbolicDirichletGeodesics.line A c t) = dist (HyperbolicDirichletGeodesics.line A c t) z := dist_comm _ _
      _ = dist (verticalPoint c t) (A • z) := HyperbolicDirichletGeodesics.dist_to_point A c t z
      _ = dist (A • z) (verticalPoint c t) := dist_comm _ _
  have h₂ : dist (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) =
      dist (verticalPoint c s) (verticalPoint c t) := by
    rw [HyperbolicDirichletGeodesics.line_distance, (vertical_isometry c).dist_eq]
  change dist (HyperbolicDirichletGeodesics.line A c s) z + dist z (HyperbolicDirichletGeodesics.line A c t) = _ ↔ _
  rw [h₀, h₁, h₂]
  exact vertical_between_iff c s t (A • z)

theorem exists_clock (s t u : ℝ) (hu : u ∈ uIcc s t) :
    ∃ v : I, HyperbolicDirichletGeodesics.clock s t v = u := by
  have hseg : u ∈ segment ℝ s t := by rwa [segment_eq_uIcc]
  rw [segment_eq_image] at hseg
  obtain ⟨v, hv, heq⟩ := hseg
  exact ⟨⟨v, hv⟩, heq⟩

theorem range_segment (A : SL2) (c s t : ℝ) :
    range (HyperbolicDirichletGeodesics.segment A c s t) =
      metricSegment (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) := by
  apply Set.Subset.antisymm
  · rintro z ⟨v, rfl⟩
    apply (normalized_between_iff A c s t _).mpr
    change (A • (A⁻¹ • verticalPoint c (HyperbolicDirichletGeodesics.clock s t v))).re = c ∧
      Real.log (A • (A⁻¹ • verticalPoint c (HyperbolicDirichletGeodesics.clock s t v))).im ∈ uIcc s t
    rw [smul_inv_smul]
    change c = c ∧ Real.log (Real.exp (HyperbolicDirichletGeodesics.clock s t v)) ∈ uIcc s t
    rw [Real.log_exp]
    exact ⟨rfl, HyperbolicDirichletGeodesics.clock_between s t v⟩
  · intro z hz
    obtain ⟨hre, hclock⟩ := (normalized_between_iff A c s t z).mp hz
    let τ := Real.log (A • z).im
    obtain ⟨v, hv⟩ := exists_clock s t τ hclock
    have hvertical : verticalPoint c τ = A • z := by
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hre.symm
      · exact Real.exp_log (A • z).im_pos
    have hline : HyperbolicDirichletGeodesics.line A c τ = z := by
      change A⁻¹ • verticalPoint c τ = z
      rw [hvertical, inv_smul_smul]
    refine ⟨v, ?_⟩
    change HyperbolicDirichletGeodesics.line A c (HyperbolicDirichletGeodesics.clock s t v) = z
    rw [hv, hline]

theorem metricSegment_subset_region (Γ : Subgroup SL2) (p a b : ℍ)
    (ha : a ∈ region Γ p) (hb : b ∈ region Γ p) : metricSegment a b ⊆ region Γ p := by
  obtain ⟨A, c, s, t, hs, ht⟩ := exists_clock_coordinates a b
  change HyperbolicDirichletGeodesics.line A c s = a at hs
  change HyperbolicDirichletGeodesics.line A c t = b at ht
  intro z hz
  have hz' : z ∈ metricSegment (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) := by
    rwa [hs, ht]
  rw [← range_segment] at hz'
  obtain ⟨v, rfl⟩ := hz'
  exact HyperbolicDirichletGeodesics.segment_mem_region Γ p A c s t (hs.symm ▸ ha) (ht.symm ▸ hb) v

end VeechDichotomy.HyperbolicCanonicalSegments
