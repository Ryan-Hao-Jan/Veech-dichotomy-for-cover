module

public import VeechDichotomy.HyperbolicEllipticLocalFiniteness
public import VeechDichotomy.HyperbolicKleinDirichlet
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual interior of a discrete Dirichlet region is exactly its
strict region. A genuine nontrivial active affine constraint cannot
contain an interior point, by the actual open mapping theorem and the
proved Klein homeomorphism. Independent-normal corners and nontrivial
elliptic points at a regular center therefore lie on the true frontier. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletInterior

open LinearGroup HyperbolicKleinMap HyperbolicKleinHomeomorph HyperbolicKleinHalfPlanes
open HyperbolicBisectorNull HyperbolicDirichletRegions HyperbolicStrictDirichlet
open HyperbolicDirichletCorners HyperbolicEllipticLocalFiniteness HyperbolicRegularCenters Set Topology
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem point_isOpenMap : IsOpenMap point := by
  have hd : IsOpen {u : ℂ | ‖u‖ < 1} := isOpen_lt continuous_norm continuous_const
  change IsOpenMap ((Subtype.val : Disk → ℂ) ∘ homeomorph)
  exact hd.isOpenMap_subtype_val.comp homeomorph.isOpenMap

theorem linearPart_ne_zero {p q : ℍ} (hpq : p ≠ q) {u : ℂ} (hu : affineForm p q u = 0) :
    linearPart p q ≠ 0 := by
  intro hzero
  have hRe := congrArg (fun f : ℂ →L[ℝ] ℝ => f 1) hzero
  have hIm := congrArg (fun f : ℂ →L[ℝ] ℝ => f Complex.I) hzero
  have hb : linear p q / 2 = 0 := by simpa [linearPart] using hRe
  have hac : (leading p q - constant p q) / 2 = 0 := by simpa [linearPart] using hIm
  have hconst : (leading p q + constant p q) / 2 = 0 := by
    simpa only [affineForm_eq, hzero, zero_apply, add_zero] using hu
  rcases coefficient_nontrivial hpq with hA | hB
  · apply hA
    linarith only [hac, hconst]
  · apply hB
    linarith only [hb]

theorem affineForm_isOpenMap {p q : ℍ} (hpq : p ≠ q) {u : ℂ} (hu : affineForm p q u = 0) :
    IsOpenMap (affineForm p q) := by
  classical
  have hn := linearPart_ne_zero hpq hu
  have hex : ∃ v : ℂ, linearPart p q v ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    apply ContinuousLinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  have hsurj : Function.Surjective (linearPart p q) := by
    intro y
    refine ⟨(y / linearPart p q v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have heq : affineForm p q = fun w : ℂ => (leading p q + constant p q) / 2 + linearPart p q w :=
    funext (affineForm_eq p q)
  rw [heq]
  exact (Homeomorph.addLeft ((leading p q + constant p q) / 2)).isOpenMap.comp ((linearPart p q).isOpenMap hsurj)

theorem active_not_interior_halfPlane {p q : ℍ} (hpq : p ≠ q) {u : ℂ}
    (hu : affineForm p q u = 0) : u ∉ interior {w : ℂ | affineForm p q w ≤ 0} := by
  intro hint
  have hopen := affineForm_isOpenMap hpq hu
  have hnhds := hopen.image_mem_nhds (mem_interior_iff_mem_nhds.mp hint)
  have hsub : affineForm p q '' {w : ℂ | affineForm p q w ≤ 0} ⊆ Iic (0 : ℝ) := by
    rintro y ⟨w, hw, rfl⟩
    exact hw
  have hbound : Iic (0 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    simpa only [hu] using Filter.mem_of_superset hnhds hsub
  have hzero : (0 : ℝ) ∈ interior (Iic (0 : ℝ)) := mem_interior_iff_mem_nhds.mpr hbound
  rw [interior_Iic] at hzero
  exact lt_irrefl (0 : ℝ) hzero

theorem active_not_interior (Γ : Subgroup SL2) (p z : ℍ) {γ : Γ}
    (hγ : γ • p ≠ p) (heq : dist z p = dist z (γ • p)) : z ∉ interior (region Γ p) := by
  intro hint
  have hu := (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mp heq
  have hImage : point z ∈ interior (point '' region Γ p) :=
    point_isOpenMap.image_interior_subset _ ⟨z, hint, rfl⟩
  have hsub : point '' region Γ p ⊆ {u : ℂ | affineForm p (γ • p) u ≤ 0} := by
    rintro _ ⟨w, hw, rfl⟩
    exact (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) w).mp (hw γ)
  exact active_not_interior_halfPlane hγ.symm hu (interior_mono hsub hImage)

theorem interior_eq_strict (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) :
    interior (region Γ p) = strictRegion Γ p := by
  apply Set.Subset.antisymm
  · intro z hz γ hγ
    have hD : z ∈ region Γ p := interior_subset hz
    have hn : dist z p ≠ dist z (γ • p) := fun heq => active_not_interior Γ p z hγ heq hz
    exact lt_of_le_of_ne (hD γ) hn
  · intro z hz
    exact HyperbolicDirichletLocalFiniteness.mem_interior_of_strict Γ p z hz

theorem corners_subset_frontier (Γ : Subgroup SL2) (p : ℍ) : corners Γ p ⊆ frontier (region Γ p) := by
  rintro z ⟨hzD, γ, δ, hd, hactive⟩
  apply (mem_frontier_iff_notMem_interior hzD).mpr
  by_cases hγ : γ • p = p
  · by_cases hδ : δ • p = p
    · apply False.elim
      apply hd
      rw [hγ, hδ]
      simp only [normalDet, sub_self]
    · exact active_not_interior Γ p z hδ ((HyperbolicKleinHalfPlanes.dist_eq_iff p (δ • p) z).mpr hactive.2)
  · exact active_not_interior Γ p z hγ ((HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mpr hactive.1)

theorem elliptic_subset_frontier (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) :
    region Γ p ∩ ellipticPoints Γ ⊆ frontier (region Γ p) := by
  rintro z ⟨hzD, γ, hnontrivial, hfix⟩
  have hγ : γ • p ≠ p := fun h => hnontrivial (hp γ h)
  have heq : dist z p = dist z (γ • p) := by
    have hi := dist_smul (γ : SL2) z p
    change dist (γ • z) (γ • p) = dist z p at hi
    rw [hfix] at hi
    exact hi.symm
  exact (mem_frontier_iff_notMem_interior hzD).mpr (active_not_interior Γ p z hγ heq)

theorem vertexCandidates_subset_frontier (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) :
    vertexCandidates Γ p ⊆ frontier (region Γ p) :=
  union_subset (corners_subset_frontier Γ p) (elliptic_subset_frontier Γ p hp)

end VeechDichotomy.HyperbolicDirichletInterior
