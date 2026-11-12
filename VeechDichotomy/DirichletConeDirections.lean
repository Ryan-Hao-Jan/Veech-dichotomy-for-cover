module

public import VeechDichotomy.KleinTangentEquivalence
public import Mathlib.Topology.Order.LeftRight

/-! Actual active-cone rays are realized by actual nearby points of the
Dirichlet region. The genuine open Klein coordinates and exact local cone
membership prove this directly. The invertible tangent map then gives a
closed convex physical cone containing every actual endpoint direction,
with every nonzero cone direction realized up to a positive factor. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletConeDirections

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicDirichletInterior
open HyperbolicKleinMap HyperbolicDirectionVectors HyperbolicTriangleAngleAddition
open KleinTangentEquivalence
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def physicalCone (Γ : Subgroup SL2) (p z : ℍ) : Set ℂ :=
  forward z '' DirichletActiveCones.cone Γ p z

theorem physical_zero_mem (Γ : Subgroup SL2) (p z : ℍ) : 0 ∈ physicalCone Γ p z :=
  ⟨0, DirichletActiveCones.zero_mem Γ p z, map_zero _⟩

theorem physical_smul_mem (Γ : Subgroup SL2) (p z : ℍ) {u : ℂ} (hu : u ∈ physicalCone Γ p z)
    {t : ℝ} (ht : 0 ≤ t) : t • u ∈ physicalCone Γ p z := by
  obtain ⟨k, hk, rfl⟩ := hu
  exact ⟨t • k, DirichletActiveCones.smul_mem Γ p z hk ht, map_smul _ _ _⟩

theorem physical_isClosed (Γ : Subgroup SL2) (p z : ℍ) : IsClosed (physicalCone Γ p z) :=
  isClosed_image z (DirichletActiveCones.isClosed_cone Γ p z)

theorem physical_convex (Γ : Subgroup SL2) (p z : ℍ) : Convex ℝ (physicalCone Γ p z) :=
  (DirichletActiveCones.convex_cone Γ p z).linear_image (forward z)

theorem direction_mem (Γ : Subgroup SL2) (p z w : ℍ) (hw : w ∈ region Γ p) : direction z w ∈ physicalCone Γ p z := by
  refine ⟨factor w • (point w - point z),
    DirichletActiveCones.smul_mem Γ p z (DirichletActiveCones.displacement_mem Γ p z w hw) (factor_pos w).le, ?_⟩
  rw [map_smul]
  exact (direction_klein z w).symm

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem ray_realized (p z : ℍ) (hz : z ∈ region Γ p) {u : ℂ}
    (hu : u ∈ DirichletActiveCones.cone Γ p z) (hne : u ≠ 0) :
    ∃ (t : ℝ) (w : ℍ), 0 < t ∧ w ∈ region Γ p ∧ w ≠ z ∧ point w - point z = t • u := by
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp (DirichletActiveCones.eventually_cone_iff Γ p z hz)
  have hImg : IsOpen (point '' U) := point_isOpenMap U hUopen
  have hcont : Continuous (fun t : ℝ => point z + t • u) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Tendsto (fun t : ℝ => point z + t • u) (𝓝 0) (𝓝 (point z)) := by
    simpa only [zero_smul, add_zero] using! (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), point z + t • u ∈ point '' U :=
    htend.eventually (hImg.mem_nhds ⟨z, hzU, rfl⟩)
  obtain ⟨t, ht, hpoint⟩ := hev.exists_gt
  obtain ⟨w, hwU, hwpoint⟩ := hpoint
  have hdiff : point w - point z = t • u := by rw [hwpoint]; abel
  have hcone : point w - point z ∈ DirichletActiveCones.cone Γ p z := by
    rw [hdiff]
    exact DirichletActiveCones.smul_mem Γ p z hu ht.le
  have hiff : w ∈ region Γ p ↔ point w - point z ∈ DirichletActiveCones.cone Γ p z := hUsub hwU
  have hwz : w ≠ z := by
    intro he
    rw [he, sub_self] at hdiff
    exact smul_ne_zero ht.ne' hne hdiff.symm
  exact ⟨t, w, ht, hiff.mpr hcone, hwz, hdiff⟩

theorem cone_direction_realized (p z : ℍ) (hz : z ∈ region Γ p) {u : ℂ}
    (hu : u ∈ DirichletActiveCones.cone Γ p z) (hne : u ≠ 0) :
    ∃ (w : ℍ) (s : ℝ), w ∈ region Γ p ∧ w ≠ z ∧ 0 < s ∧ direction z w = s • forward z u := by
  obtain ⟨t, w, ht, hw, hwz, hdiff⟩ := ray_realized Γ p z hz hu hne
  refine ⟨w, factor w * t, hw, hwz, mul_pos (factor_pos w) ht, ?_⟩
  rw [direction_klein, hdiff, map_smul, smul_smul]

theorem physical_direction_realized (p z : ℍ) (hz : z ∈ region Γ p) {u : ℂ}
    (hu : u ∈ physicalCone Γ p z) (hne : u ≠ 0) :
    ∃ (w : ℍ) (s : ℝ), w ∈ region Γ p ∧ w ≠ z ∧ 0 < s ∧ direction z w = s • u := by
  obtain ⟨k, hk, rfl⟩ := hu
  have hkne : k ≠ 0 := by intro he; rw [he, map_zero] at hne; exact hne rfl
  exact cone_direction_realized Γ p z hz hk hkne

theorem physical_interior_nonempty (p z : ℍ) : (interior (physicalCone Γ p z)).Nonempty := by
  obtain ⟨u, hu⟩ := DirichletActiveCones.cone_interior_nonempty Γ p z
  refine ⟨forward z u, ?_⟩
  change forward z u ∈ interior (forward z '' DirichletActiveCones.cone Γ p z)
  rw [← image_interior]
  exact ⟨u, hu, rfl⟩

end VeechDichotomy.DirichletConeDirections
