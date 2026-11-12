module

public import VeechDichotomy.HyperbolicRegionAngles

/-! The actual active nontrivial distance constraints at a point form
a finite set. Near a genuine Dirichlet point, all inactive constraints
remain automatic; exact membership is determined by these actual active
constraints alone. Their affine forms equal their linear parts on Klein
displacements from the point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletActiveConstraints

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicDirichletLocalFiniteness
open HyperbolicKleinMap HyperbolicKleinHalfPlanes
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def active (Γ : Subgroup SL2) (p z : ℍ) : Set Γ :=
  {γ | γ • p ≠ p ∧ dist z p = dist z (γ • p)}

theorem active_subset_nearby (Γ : Subgroup SL2) (p z : ℍ) : active Γ p z ⊆ nearby Γ p z := by
  intro γ hγ
  change dist (γ • p) z ≤ dist z p + 2
  rw [dist_comm, ← hγ.2]
  linarith

theorem active_form_shift (Γ : Subgroup SL2) (p z : ℍ) {γ : Γ} (hγ : γ ∈ active Γ p z) (w : ℍ) :
    affineForm p (γ • p) (point w) = linearPart p (γ • p) (point w - point z) := by
  have hz := (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mp hγ.2
  rw [affineForm_eq] at hz ⊢
  rw [map_sub]
  linarith

theorem active_normal_ne_zero (Γ : Subgroup SL2) (p z : ℍ) {γ : Γ} (hγ : γ ∈ active Γ p z) :
    linearPart p (γ • p) ≠ 0 :=
  HyperbolicDirichletInterior.linearPart_ne_zero hγ.1.symm
    ((HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mp hγ.2)

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem active_finite (p z : ℍ) : (active Γ p z).Finite :=
  (nearby_finite Γ p z).subset (active_subset_nearby Γ p z)

theorem active_nonempty_of_frontier (p : ℍ) {z : ℍ} (hz : z ∈ frontier (region Γ p)) :
    (active Γ p z).Nonempty := by
  obtain ⟨γ, hγ, heq⟩ := frontier_mem_bisector Γ p hz
  exact ⟨γ, hγ, heq⟩

theorem eventually_active_iff (p z : ℍ) (hz : z ∈ region Γ p) :
    ∀ᶠ w in 𝓝 z, w ∈ region Γ p ↔ ∀ γ ∈ active Γ p z, dist w p ≤ dist w (γ • p) := by
  have hev : ∀ᶠ w in 𝓝 z, ∀ γ ∈ nearby Γ p z,
      γ ∉ active Γ p z → dist w p ≤ dist w (γ • p) := by
    apply (nearby_finite Γ p z).eventually_all.mpr
    intro γ _
    by_cases hfix : γ • p = p
    · exact Eventually.of_forall (fun w _ => by rw [hfix])
    by_cases hact : γ ∈ active Γ p z
    · exact Eventually.of_forall (fun _ hnot => False.elim (hnot hact))
    have hneq : dist z p ≠ dist z (γ • p) := fun he => hact ⟨hfix, he⟩
    have hstrict : dist z p < dist z (γ • p) := lt_of_le_of_ne (hz γ) hneq
    have ht : ∀ᶠ w in 𝓝 z, dist w p < dist w (γ • p) :=
      (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)).mem_nhds hstrict
    exact ht.mono (fun _ hw _ => hw.le)
  filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 2), hev] with w hw hnear
  constructor
  · intro hD γ _
    exact hD γ
  · intro hactive
    apply (region_iff_nearby Γ p z hw).mpr
    intro γ hγ
    by_cases hact : γ ∈ active Γ p z
    · exact hactive γ hact
    · exact hnear γ hγ hact

end VeechDichotomy.DirichletActiveConstraints
