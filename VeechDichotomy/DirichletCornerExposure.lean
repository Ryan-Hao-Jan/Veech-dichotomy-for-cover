module

public import VeechDichotomy.NativeDirichletPolygonDeficit
public import VeechDichotomy.HyperbolicDirichletCorners

/-! Every genuine Dirichlet corner is exposed by an actual real linear
functional in Klein coordinates. The sum of its two independent active
constraints has a unique maximum there. Thus the actual corner cannot
lie in the convex hull of any other points of the actual Dirichlet region. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerExposure

open LinearGroup Set HyperbolicKleinMap HyperbolicKleinHalfPlanes HyperbolicDirichletRegions
open HyperbolicDirichletCorners
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem exposed (Γ : Subgroup SL2) (p v : ℍ) (hv : v ∈ corners Γ p) :
    ∃ L : ℂ →L[ℝ] ℝ, ∀ z ∈ region Γ p, z ≠ v → L (point z) < L (point v) := by
  obtain ⟨_, γ, δ, hd, hvI⟩ := hv
  let L := linearPart p (γ • p) + linearPart p (δ • p)
  have hid (z : ℍ) : L (point z) - L (point v) =
      affineForm p (γ • p) (point z) + affineForm p (δ • p) (point z) := by
    have hγ := hvI.1
    have hδ := hvI.2
    rw [affineForm_eq] at hγ hδ
    simp only [L, add_apply, affineForm_eq]
    linarith
  refine ⟨L, ?_⟩
  intro z hz hne
  have hγ : affineForm p (γ • p) (point z) ≤ 0 :=
    (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) z).mp (hz γ)
  have hδ : affineForm p (δ • p) (point z) ≤ 0 :=
    (HyperbolicKleinHalfPlanes.dist_le_iff p (δ • p) z).mp (hz δ)
  have hle : L (point z) ≤ L (point v) := by linarith only [hid z, hγ, hδ]
  apply lt_of_le_of_ne hle
  intro he
  have hzγ : affineForm p (γ • p) (point z) = 0 := by linarith only [hid z, hγ, hδ, he]
  have hzδ : affineForm p (δ • p) (point z) = 0 := by linarith only [hid z, hγ, hδ, he]
  exact hne (intersection_subsingleton hd ⟨hzγ, hzδ⟩ hvI)

theorem not_mem_hull_rest (Γ : Subgroup SL2) (p v : ℍ) (hv : v ∈ corners Γ p) :
    point v ∉ convexHull ℝ (point '' (region Γ p \ {v})) := by
  obtain ⟨L, hL⟩ := exposed Γ p v hv
  have hsub : point '' (region Γ p \ {v}) ⊆ L ⁻¹' Iio (L (point v)) := by
    rintro _ ⟨z, ⟨hz, hne⟩, rfl⟩
    exact hL z hz (by simpa only [mem_singleton_iff] using hne)
  have hbound : convexHull ℝ (point '' (region Γ p \ {v})) ⊆ L ⁻¹' Iio (L (point v)) :=
    convexHull_min hsub ((convex_Iio _).linear_preimage L.toLinearMap)
  intro hp
  have he : L (point v) < L (point v) := hbound hp
  exact (lt_irrefl _) he

end VeechDichotomy.DirichletCornerExposure
