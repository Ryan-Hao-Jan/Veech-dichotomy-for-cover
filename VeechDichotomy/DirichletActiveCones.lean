module

public import VeechDichotomy.DirichletActiveConstraints

/-! The actual active Klein inequalities define a genuine closed convex
cone with nonempty interior. Globally all Dirichlet displacements lie in
it, and locally its inequalities are exactly the actual region. At a
boundary point it lies in a genuine nonzero supporting half-plane. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletActiveCones

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicKleinMap HyperbolicKleinHalfPlanes
open DirichletActiveConstraints
open scoped UpperHalfPlane

def cone (Γ : Subgroup SL2) (p z : ℍ) : Set ℂ :=
  {u | ∀ γ ∈ active Γ p z, linearPart p (γ • p) u ≤ 0}

theorem zero_mem (Γ : Subgroup SL2) (p z : ℍ) : 0 ∈ cone Γ p z := by
  intro γ _
  simp

theorem add_mem (Γ : Subgroup SL2) (p z : ℍ) {u v : ℂ} (hu : u ∈ cone Γ p z) (hv : v ∈ cone Γ p z) :
    u + v ∈ cone Γ p z := by
  intro γ hγ
  rw [map_add]
  exact add_nonpos (hu γ hγ) (hv γ hγ)

theorem smul_mem (Γ : Subgroup SL2) (p z : ℍ) {u : ℂ} (hu : u ∈ cone Γ p z) {t : ℝ} (ht : 0 ≤ t) :
    t • u ∈ cone Γ p z := by
  intro γ hγ
  rw [map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hu γ hγ)

theorem cone_eq_inter (Γ : Subgroup SL2) (p z : ℍ) :
    cone Γ p z = ⋂ γ : active Γ p z, {u : ℂ | linearPart p (γ.val • p) u ≤ 0} := by
  ext u
  simp [cone]

theorem isClosed_cone (Γ : Subgroup SL2) (p z : ℍ) : IsClosed (cone Γ p z) := by
  rw [cone_eq_inter]
  exact isClosed_iInter (fun γ => isClosed_le (linearPart p (γ.val • p)).continuous continuous_const)

theorem convex_cone (Γ : Subgroup SL2) (p z : ℍ) : Convex ℝ (cone Γ p z) := by
  rw [cone_eq_inter]
  exact convex_iInter (fun γ => (convex_Iic (0 : ℝ)).linear_preimage (linearPart p (γ.val • p)).toLinearMap)

theorem displacement_mem (Γ : Subgroup SL2) (p z w : ℍ) (hw : w ∈ region Γ p) :
    point w - point z ∈ cone Γ p z := by
  intro γ hγ
  rw [← active_form_shift Γ p z hγ w]
  exact (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) w).mp (hw γ)

theorem center_strict (Γ : Subgroup SL2) (p z : ℍ) {γ : Γ} (hγ : γ ∈ active Γ p z) :
    linearPart p (γ • p) (point p - point z) < 0 := by
  rw [← active_form_shift Γ p z hγ p]
  apply (HyperbolicKleinHalfPlanes.dist_lt_iff p (γ • p) p).mp
  rw [dist_self]
  exact dist_pos.mpr hγ.1.symm

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem eventually_cone_iff (p z : ℍ) (hz : z ∈ region Γ p) :
    ∀ᶠ w in 𝓝 z, w ∈ region Γ p ↔ point w - point z ∈ cone Γ p z := by
  filter_upwards [eventually_active_iff Γ p z hz] with w hw
  rw [hw]
  change (∀ γ ∈ active Γ p z, dist w p ≤ dist w (γ • p)) ↔
    ∀ γ ∈ active Γ p z, linearPart p (γ • p) (point w - point z) ≤ 0
  apply forall_congr'
  intro γ
  apply forall_congr'
  intro hγ
  rw [HyperbolicKleinHalfPlanes.dist_le_iff, active_form_shift Γ p z hγ w]

theorem center_mem_interior_cone (p z : ℍ) : point p - point z ∈ interior (cone Γ p z) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hev : ∀ᶠ u in 𝓝 (point p - point z), ∀ γ ∈ active Γ p z, linearPart p (γ • p) u < 0 := by
    apply (active_finite Γ p z).eventually_all.mpr
    intro γ hγ
    exact (isOpen_lt (linearPart p (γ • p)).continuous continuous_const).mem_nhds (center_strict Γ p z hγ)
  filter_upwards [hev] with u hu
  exact fun γ hγ => (hu γ hγ).le

theorem cone_interior_nonempty (p z : ℍ) : (interior (cone Γ p z)).Nonempty :=
  ⟨point p - point z, center_mem_interior_cone Γ p z⟩

theorem boundary_support (p : ℍ) {z : ℍ} (hz : z ∈ frontier (region Γ p)) :
    ∃ L : ℂ →L[ℝ] ℝ, L ≠ 0 ∧ cone Γ p z ⊆ {u : ℂ | L u ≤ 0} := by
  obtain ⟨γ, hγ⟩ := active_nonempty_of_frontier Γ p hz
  exact ⟨linearPart p (γ • p), active_normal_ne_zero Γ p z hγ, fun _ hu => hu γ hγ⟩

end VeechDichotomy.DirichletActiveCones
