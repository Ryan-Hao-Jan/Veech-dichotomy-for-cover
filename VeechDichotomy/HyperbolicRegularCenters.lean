module

public import VeechDichotomy.HyperbolicBisectorNull
public import VeechDichotomy.HyperbolicAreaSupport
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-! A genuine center avoiding every nontrivial elliptic fixed point
exists for each countable SL2 subgroup. Nontrivial orientation-preserving
maps have at most one fixed point in the upper half-plane; actual area
nullness excludes their countable union. The resulting center's stabilizer
acts trivially everywhere, so no generic-center oracle is introduced. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicRegularCenters

open LinearGroup Set MeasureTheory
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem fixedSet_subsingleton (A : SL2) (hnot : ¬ ∀ z : ℍ, A • z = z) :
    {z : ℍ | A • z = z}.Subsingleton := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ A
  have hpos : 0 < g.val.det := by
    change 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [A.property]
    norm_num
  have hcenter : g ∉ Subgroup.center _ := by
    intro hc
    apply hnot
    exact UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mpr hc
  intro z hz w hw
  have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hpos hcenter ⟨z, hz⟩
  exact ((UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).mp hz).trans
    ((UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).mp hw).symm

theorem fixedSet_null (A : SL2) (hnot : ¬ ∀ z : ℍ, A • z = z) : volume {z : ℍ | A • z = z} = 0 := by
  let F : Set ℍ := {z | A • z = z}
  have hc : (UpperHalfPlane.coe '' F).Countable := (fixedSet_subsingleton A hnot).countable.image _
  have hnull : (volume : Measure ℂ) (UpperHalfPlane.coe '' F) = 0 := hc.measure_zero volume
  apply measure_mono_null (t := UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' F)) _
    (HyperbolicBisectorNull.volume_preimage_null hnull)
  intro z hz
  exact ⟨z, hz, rfl⟩

variable (Γ : Subgroup SL2)

def RegularCenter (p : ℍ) : Prop := ∀ γ : Γ, γ • p = p → ∀ z : ℍ, γ • z = z

def badCenters : Set ℍ := ⋃ γ : {γ : Γ | ¬ ∀ z : ℍ, γ • z = z}, {p : ℍ | γ.val • p = p}

theorem badCenters_null [Countable Γ] : volume (badCenters Γ) = 0 :=
  measure_iUnion_null (fun γ => fixedSet_null γ.val.val γ.property)

theorem regular_of_not_bad {p : ℍ} (hp : p ∉ badCenters Γ) : RegularCenter Γ p := by
  classical
  intro γ hγ
  by_contra hnot
  exact hp (mem_iUnion.mpr ⟨⟨γ, hnot⟩, hγ⟩)

theorem exists_regular_center [Countable Γ] : ∃ p : ℍ, RegularCenter Γ p := by
  classical
  have hex : ∃ p : ℍ, p ∉ badCenters Γ := by
    by_contra hn
    push Not at hn
    have hall : badCenters Γ = univ := by
      ext p
      constructor
      · intro _
        exact mem_univ p
      · intro _
        exact hn p
    have hz := badCenters_null Γ
    rw [hall] at hz
    exact (isOpen_univ.measure_ne_zero (volume : Measure ℍ) univ_nonempty) hz
  obtain ⟨p, hp⟩ := hex
  exact ⟨p, regular_of_not_bad Γ hp⟩

end VeechDichotomy.HyperbolicRegularCenters
