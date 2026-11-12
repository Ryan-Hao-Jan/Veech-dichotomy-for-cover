module

public import VeechDichotomy.HyperbolicKleinHalfPlanes
public import VeechDichotomy.HyperbolicStrictDirichlet

/-! Genuine ordinary and strict Dirichlet regions have convex images
under the constructed actual Klein homeomorphism. Their images are
exactly the disk intersected with their actual affine constraints.
This uses no discreteness, finite-area, polygon or convexity oracle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinDirichlet

open LinearGroup HyperbolicKleinMap HyperbolicKleinHomeomorph HyperbolicKleinHalfPlanes
open HyperbolicDirichletRegions HyperbolicStrictDirichlet Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

variable (Γ : Subgroup SL2)

def diskRegion (p : ℍ) : Set ℂ :=
  Metric.ball 0 1 ∩ ⋂ γ : Γ, {u : ℂ | affineForm p (γ • p) u ≤ 0}

def strictDiskRegion (p : ℍ) : Set ℂ :=
  Metric.ball 0 1 ∩ ⋂ γ : {γ : Γ | γ • p ≠ p}, {u : ℂ | affineForm p (γ.val • p) u < 0}

theorem image_region (p : ℍ) : point '' region Γ p = diskRegion Γ p := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z, ?_⟩
    exact mem_iInter.mpr (fun γ => (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) z).mp (hz γ))
  · intro u hu
    let v : Disk := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu.1⟩
    let z := inverse v
    have heq : point z = u := congrArg Subtype.val (forward_inverse v)
    refine ⟨z, ?_, heq⟩
    intro γ
    apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) z).mpr
    rw [heq]
    exact mem_iInter.mp hu.2 γ

theorem image_strictRegion (p : ℍ) : point '' strictRegion Γ p = strictDiskRegion Γ p := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z, ?_⟩
    exact mem_iInter.mpr (fun γ => (HyperbolicKleinHalfPlanes.dist_lt_iff p (γ.val • p) z).mp (hz γ.val γ.property))
  · intro u hu
    let v : Disk := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu.1⟩
    let z := inverse v
    have heq : point z = u := congrArg Subtype.val (forward_inverse v)
    refine ⟨z, ?_, heq⟩
    intro γ hγ
    apply (HyperbolicKleinHalfPlanes.dist_lt_iff p (γ • p) z).mpr
    rw [heq]
    exact mem_iInter.mp hu.2 (⟨γ, hγ⟩ : {γ : Γ | γ • p ≠ p})

theorem convex_diskRegion (p : ℍ) : Convex ℝ (diskRegion Γ p) :=
  (convex_ball _ _).inter (convex_iInter (fun γ : Γ => convex_halfPlane p (γ • p)))

theorem convex_strictDiskRegion (p : ℍ) : Convex ℝ (strictDiskRegion Γ p) :=
  (convex_ball _ _).inter (convex_iInter (fun γ : {γ : Γ | γ • p ≠ p} => convex_strictHalfPlane p (γ.val • p)))

theorem convex_image_region (p : ℍ) : Convex ℝ (point '' region Γ p) := by
  rw [image_region]
  exact convex_diskRegion Γ p

theorem convex_image_strictRegion (p : ℍ) : Convex ℝ (point '' strictRegion Γ p) := by
  rw [image_strictRegion]
  exact convex_strictDiskRegion Γ p

end VeechDichotomy.HyperbolicKleinDirichlet
