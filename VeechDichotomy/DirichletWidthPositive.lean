module

public import VeechDichotomy.DirichletPhysicalFan

/-! Genuine Dirichlet angular widths are positive. At a true corner
the nonzero center direction is interior to the physical cone, so a
small actual transverse perturbation gives a positive angle. Elsewhere
the already proved width is pi. True corners therefore have width in
the exact open interval (0,pi). -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletWidthPositive

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicKleinMap HyperbolicGeodesicHulls DirichletPointedCones DirichletConeDirections
open KleinTangentEquivalence DirichletCornerAngles HyperbolicRegionAngles ComplexOrientedTriangles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem corner_width_pos (p z : ℍ) (hz : z ∈ corners Γ p) : 0 < width Γ p z := by
  let u := forward z (point p - point z)
  have hdiff : point p - point z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact corner_ne_center Γ p z hz (point_injective he).symm
  have hune : u ≠ 0 := fun he => hdiff ((forward_eq_zero_iff z _).mp he)
  have hu : u ∈ interior (physicalCone Γ p z) := by
    change forward z (point p - point z) ∈ interior (forward z '' DirichletActiveCones.cone Γ p z)
    rw [← image_interior]
    exact ⟨point p - point z, DirichletActiveCones.center_mem_interior_cone Γ p z, rfl⟩
  have hcont : Continuous (fun t : ℝ => u + t • (Complex.I * u)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Tendsto (fun t : ℝ => u + t • (Complex.I * u)) (𝓝 0) (𝓝 u) := by
    simpa only [zero_smul, add_zero] using! (hcont.continuousAt (x := (0 : ℝ))).tendsto
  obtain ⟨t, ht, htv⟩ := (htend.eventually (isOpen_interior.mem_nhds hu)).exists_gt
  let v := u + t • (Complex.I * u)
  have hcrossEq : cross u v = t * Complex.normSq u := by
    simp [v, cross, Complex.real_smul, Complex.normSq_apply]
    ring
  have hN : 0 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hune)
  have hcross : 0 < cross u v := by rw [hcrossEq]; exact mul_pos ht hN
  have hvne : v ≠ 0 := by
    intro he
    rw [he] at hcross
    simp only [cross, Complex.zero_re, Complex.zero_im, mul_zero, sub_self, lt_self_iff_false] at hcross
  have hang : 0 < InnerProductGeometry.angle u v := by
    apply lt_of_le_of_ne (InnerProductGeometry.angle_nonneg u v)
    intro he
    obtain ⟨_, r, _, hvr⟩ := InnerProductGeometry.angle_eq_zero_iff.mp he.symm
    have hc : cross u (r • u) = 0 := by simp [cross, Complex.real_smul]; ring
    rw [hvr, hc] at hcross
    exact lt_irrefl _ hcross
  have hl : InnerProductGeometry.angle u v ≤ vectorWidth (physicalCone Γ p z) :=
    le_csSup (vectorValues_bddAbove _) (Or.inr ⟨u, v, interior_subset hu, interior_subset htv, hune, hvne, rfl⟩)
  rw [DirichletConeAngles.width_eq Γ p z hz.1]
  exact hang.trans_le hl

theorem corner_width_range (p z : ℍ) (hz : z ∈ corners Γ p) : 0 < width Γ p z ∧ width Γ p z < Real.pi :=
  ⟨corner_width_pos Γ p z hz, DirichletCornerWidth.width_lt_pi Γ p z hz⟩

theorem width_pos (p z : ℍ) (hz : z ∈ region Γ p) : 0 < width Γ p z := by
  by_cases hc : z ∈ corners Γ p
  · exact corner_width_pos Γ p z hc
  · rw [DirichletNoncornerWidth.width_eq_pi Γ p z hz hc]
    exact Real.pi_pos

end VeechDichotomy.DirichletWidthPositive
