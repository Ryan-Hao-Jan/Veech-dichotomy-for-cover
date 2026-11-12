module

public import VeechDichotomy.DirichletCornerWidth

/-! Every actual noncorner point of a discrete Dirichlet region has
angular width pi and deficit zero. Without two independent active
normals their common kernel contains a genuine line; both physical
directions are actually realized by region points. Thus positive actual
deficit characterizes precisely the actual true corners. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletNoncornerWidth

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicKleinMap
open HyperbolicKleinHalfPlanes DirichletActiveConstraints DirichletActiveCones DirichletConeDirections
open KleinTangentEquivalence HyperbolicRegionAngles DirichletCornerAngles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem noncorner_has_line (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) (hn : z ∉ corners Γ p) :
    ∃ u : ℂ, u ≠ 0 ∧ u ∈ cone Γ p z ∧ -u ∈ cone Γ p z := by
  by_cases hactive : (active Γ p z).Nonempty
  · obtain ⟨γ, hγ⟩ := hactive
    let u : ℂ := ⟨-normalIm p (γ • p), normalRe p (γ • p)⟩
    have hdet (η : Γ) (hη : η ∈ active Γ p z) : normalDet p (γ • p) (η • p) = 0 := by
      by_contra hd
      exact hn ⟨hz, γ, η, hd,
        (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mp hγ.2,
        (HyperbolicKleinHalfPlanes.dist_eq_iff p (η • p) z).mp hη.2⟩
    have hlin (η : Γ) (hη : η ∈ active Γ p z) : linearPart p (η • p) u = 0 := by
      have hd := hdet η hη
      simp only [linearPart, add_apply, smul_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
      change normalRe p (η • p) * (-normalIm p (γ • p)) + normalIm p (η • p) * normalRe p (γ • p) = 0
      dsimp only [normalDet] at hd
      nlinarith only [hd]
    have hune : u ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      have him := congrArg Complex.im he
      change -normalIm p (γ • p) = 0 at hre
      change normalRe p (γ • p) = 0 at him
      have hI : normalIm p (γ • p) = 0 := neg_eq_zero.mp hre
      apply active_normal_ne_zero Γ p z hγ
      ext w
      simp only [linearPart, add_apply, smul_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
      change normalRe p (γ • p) * w.re + normalIm p (γ • p) * w.im = 0
      rw [him, hI]
      ring
    refine ⟨u, hune, (fun η hη => (hlin η hη).le), ?_⟩
    intro η hη
    rw [map_neg, hlin η hη, neg_zero]
  · exact ⟨1, by norm_num, (fun γ hγ => False.elim (hactive ⟨γ, hγ⟩)),
      (fun γ hγ => False.elim (hactive ⟨γ, hγ⟩))⟩

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem width_eq_pi (p z : ℍ) (hz : z ∈ region Γ p) (hn : z ∉ corners Γ p) : width Γ p z = Real.pi := by
  obtain ⟨u, hune, hu, hneg⟩ := noncorner_has_line Γ p z hz hn
  have hfne : forward z u ≠ 0 := fun he => hune ((forward_eq_zero_iff z u).mp he)
  have hfu : forward z u ∈ physicalCone Γ p z := ⟨u, hu, rfl⟩
  have hfneg : -forward z u ∈ physicalCone Γ p z := ⟨-u, hneg, map_neg _ _⟩
  have hpi : Real.pi ∈ vectorValues (physicalCone Γ p z) := Or.inr
    ⟨forward z u, -forward z u, hfu, hfneg, hfne, neg_ne_zero.mpr hfne,
      (InnerProductGeometry.angle_self_neg_of_nonzero hfne).symm⟩
  rw [DirichletConeAngles.width_eq Γ p z hz]
  exact le_antisymm (vectorWidth_le_pi _) (le_csSup (vectorValues_bddAbove _) hpi)

theorem deficit_zero (p z : ℍ) (hz : z ∈ region Γ p) (hn : z ∉ corners Γ p) : deficit Γ p z = 0 := by
  rw [DirichletCornerAngles.deficit, width_eq_pi Γ p z hz hn, sub_self]

theorem deficit_pos_iff (p z : ℍ) (hz : z ∈ region Γ p) : 0 < deficit Γ p z ↔ z ∈ corners Γ p := by
  constructor
  · intro hp
    by_contra hn
    rw [deficit_zero Γ p z hz hn] at hp
    exact lt_irrefl _ hp
  · exact DirichletCornerWidth.deficit_pos Γ p z

end VeechDichotomy.DirichletNoncornerWidth
