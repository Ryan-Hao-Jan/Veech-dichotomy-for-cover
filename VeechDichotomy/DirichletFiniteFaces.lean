module

public import VeechDichotomy.NativeDirichletFiniteHull
public import Mathlib.Data.Set.Finite.Powerset

/-! The actual intersections of the actual closed Dirichlet region
with all its actual bisectors form a finite family. Each is a compact
extreme face and is exactly the convex hull of the actual vertices it
contains. Finiteness follows from the finite set of vertex subsets. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletFiniteFaces

open LinearGroup NativeVeech Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicKleinHalfPlanes DirichletKleinClosure DirichletExtremePoints
open scoped UpperHalfPlane

def face (Γ : Subgroup SL2) (p : ℍ) (γ : Γ) : Set ℂ :=
  closedRegion Γ p ∩ {u | affineForm p (γ • p) u = 0}

theorem form_mix (p q : ℍ) (x y : ℂ) (a b : ℝ) (hab : a + b = 1) :
    affineForm p q (a • x + b • y) = a * affineForm p q x + b * affineForm p q y := by
  simp only [affineForm_eq, map_add, map_smul, smul_eq_mul]
  calc
    _ = (a + b) * ((HyperbolicBisectorNull.leading p q + HyperbolicBisectorNull.constant p q) / 2) +
        (a * linearPart p q x + b * linearPart p q y) := by rw [hab]; ring
    _ = _ := by ring

theorem isCompact_face (Γ : Subgroup SL2) (p : ℍ) (γ : Γ) : IsCompact (face Γ p γ) := by
  have hc : Continuous (affineForm p (γ • p)) := by unfold affineForm; fun_prop
  exact (isCompact_closedRegion Γ p).inter_right (isClosed_eq hc continuous_const)

theorem convex_face (Γ : Subgroup SL2) (p : ℍ) (γ : Γ) : Convex ℝ (face Γ p γ) := by
  have he : {u : ℂ | affineForm p (γ • p) u = 0} = (linearPart p (γ • p)) ⁻¹'
      {-(HyperbolicBisectorNull.leading p (γ • p) + HyperbolicBisectorNull.constant p (γ • p)) / 2} := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, affineForm_eq]
    constructor <;> intro h <;> linarith
  unfold face
  rw [he]
  exact (convex_closedRegion Γ p).inter ((convex_singleton _).linear_preimage (linearPart p (γ • p)).toLinearMap)

theorem isExtreme_face (Γ : Subgroup SL2) (p : ℍ) (γ : Γ) :
    IsExtreme ℝ (closedRegion Γ p) (face Γ p γ) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hxle := DirichletIdealRadialPoints.closure_halfPlane Γ p hx γ
  have hyle := DirichletIdealRadialPoints.closure_halfPlane Γ p hy γ
  have hsum : a * affineForm p (γ • p) x + b * affineForm p (γ • p) y = 0 := by
    rw [← form_mix p (γ • p) x y a b hab, he]
    exact hz.2
  have hprod : a * affineForm p (γ • p) x = 0 := by
    have hl := mul_nonpos_of_nonneg_of_nonpos ha.le hxle
    have hr := mul_nonpos_of_nonneg_of_nonpos hb.le hyle
    linarith only [hsum, hl, hr]
  exact ⟨hx, (mul_eq_zero.mp hprod).resolve_left ha.ne'⟩

theorem face_eq_convexHull (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (γ : Γ) :
    face Γ p γ = convexHull ℝ (vertices Γ p ∩ face Γ p γ) := by
  let : DiscreteTopology Γ := hΓ.1
  have hf : (vertices Γ p ∩ face Γ p γ).Finite :=
    (NativeDirichletFiniteHull.vertices_finite Γ hΓ p hp).subset inter_subset_left
  have hext : (face Γ p γ).extremePoints ℝ ⊆ vertices Γ p ∩ face Γ p γ := by
    intro u hu
    exact ⟨extremePoints_subset_vertices Γ p ((isExtreme_face Γ p γ).extremePoints_subset_extremePoints hu), hu.1⟩
  apply Subset.antisymm
  · calc
      _ = closure (convexHull ℝ ((face Γ p γ).extremePoints ℝ)) :=
        (closure_convexHull_extremePoints (isCompact_face Γ p γ) (convex_face Γ p γ)).symm
      _ ⊆ closure (convexHull ℝ (vertices Γ p ∩ face Γ p γ)) := closure_mono (convexHull_mono hext)
      _ = _ := (hf.isCompact_convexHull ℝ).isClosed.closure_eq
  · exact convexHull_min inter_subset_right (convex_face Γ p γ)

theorem faces_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (range (face Γ p)).Finite := by
  have hf := (NativeDirichletFiniteHull.vertices_finite Γ hΓ p hp).finite_subsets
  apply (hf.image (convexHull ℝ)).subset
  rintro F ⟨γ, rfl⟩
  exact ⟨vertices Γ p ∩ face Γ p γ, inter_subset_left, (face_eq_convexHull Γ hΓ p hp γ).symm⟩

def sides (Γ : Subgroup SL2) (p : ℍ) : Set (Set ℂ) :=
  {F | ∃ γ : Γ, γ • p ≠ p ∧ F = face Γ p γ ∧ F.Nontrivial}

theorem sides_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (sides Γ p).Finite := by
  apply (faces_finite Γ hΓ p hp).subset
  rintro F ⟨γ, _, rfl, _⟩
  exact mem_range_self γ

end VeechDichotomy.DirichletFiniteFaces
