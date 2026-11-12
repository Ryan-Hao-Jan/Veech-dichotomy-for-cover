module

public import VeechDichotomy.NativeDirichletFiniteCorners

/-! Actual radial points approaching the ideal boundary of a genuine
Dirichlet region. Every ideal closure point satisfies all actual closed
Klein half-planes, and its strict radial combinations with the actual
center are genuine region points in the open disk. This does not assume
finiteness of the ideal boundary or an ideal-polygon area formula. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletIdealRadialPoints

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicKleinMap
open HyperbolicKleinHomeomorph HyperbolicKleinHalfPlanes
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def idealBoundary (Γ : Subgroup SL2) (p : ℍ) : Set ℂ :=
  {u | u ∈ closure (point '' region Γ p) ∧ ‖u‖ = 1}

theorem closure_halfPlane (Γ : Subgroup SL2) (p : ℍ) {u : ℂ}
    (hu : u ∈ closure (point '' region Γ p)) (γ : Γ) : affineForm p (γ • p) u ≤ 0 := by
  have hc : Continuous (affineForm p (γ • p)) := by
    unfold affineForm
    fun_prop
  have hsub : point '' region Γ p ⊆ {w : ℂ | affineForm p (γ • p) w ≤ 0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) z).mp (hz γ)
  exact closure_minimal hsub (isClosed_le hc continuous_const) hu

def radial (p : ℍ) (u : ℂ) (t : ℝ) : ℂ := (1 - t) • point p + t • u

theorem radial_norm_lt (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖radial p u t‖ < 1 := by
  have hcalc : ‖radial p u t‖ ≤ (1 - t) * ‖point p‖ + t := by
    calc
      _ ≤ ‖(1 - t) • point p‖ + ‖t • u‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht₁.le), abs_of_nonneg ht₀, hu, mul_one]
  have hprod := mul_pos (sub_pos.mpr ht₁) (sub_pos.mpr (norm_point_lt_one p))
  nlinarith only [hcalc, hprod]

def radialPoint (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) : ℍ :=
  inverse ⟨radial p u t, radial_norm_lt p u hu t ht₀ ht₁⟩

theorem point_radialPoint (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    point (radialPoint p u hu t ht₀ ht₁) = radial p u t :=
  congrArg Subtype.val (forward_inverse ⟨radial p u t, radial_norm_lt p u hu t ht₀ ht₁⟩)

theorem radialPoint_mem_region (Γ : Subgroup SL2) (p : ℍ) {u : ℂ} (hu : u ∈ idealBoundary Γ p)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) : radialPoint p u hu.2 t ht₀ ht₁ ∈ region Γ p := by
  intro γ
  apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) _).mpr
  rw [point_radialPoint]
  have hp := (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) p).mp (center_mem Γ p γ)
  exact (convex_halfPlane p (γ • p)) hp (closure_halfPlane Γ p hu.1 γ)
    (sub_nonneg.mpr ht₁.le) ht₀ (by ring)

theorem continuous_radial (p : ℍ) (u : ℂ) : Continuous (radial p u) := by unfold radial; fun_prop

theorem tendsto_radial_at_one (p : ℍ) (u : ℂ) : Tendsto (radial p u) (𝓝 1) (𝓝 u) := by
  simpa only [radial, sub_self, zero_smul, one_smul, zero_add] using!
    ((continuous_radial p u).continuousAt (x := (1 : ℝ))).tendsto

end VeechDichotomy.DirichletIdealRadialPoints
