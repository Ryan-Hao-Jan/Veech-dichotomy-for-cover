module

public import VeechDichotomy.NativeFiniteCornerPolygons

/-! Actual angular width at a Dirichlet boundary point: the supremum
of the fixed intrinsic angles between genuine nonzero directions to
points of the actual region. Polygon angles are bounded by this actual
width. Local wedge attainment and vertex-cycle identities are not assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerAngles

open LinearGroup Set HyperbolicDirichletRegions HyperbolicIntrinsicAngles
open scoped UpperHalfPlane

def values (Γ : Subgroup SL2) (p w : ℍ) : Set ℝ := {0} ∪
  {θ | ∃ a b : ℍ, a ∈ region Γ p ∧ b ∈ region Γ p ∧ a ≠ w ∧ b ≠ w ∧ θ = angleAt w a b}

def width (Γ : Subgroup SL2) (p w : ℍ) : ℝ := sSup (values Γ p w)
def deficit (Γ : Subgroup SL2) (p w : ℍ) : ℝ := Real.pi - width Γ p w

theorem values_nonempty (Γ : Subgroup SL2) (p w : ℍ) : (values Γ p w).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem values_le_pi (Γ : Subgroup SL2) (p w : ℍ) : ∀ θ ∈ values Γ p w, θ ≤ Real.pi := by
  rintro θ (hzero | ⟨a, b, _, _, _, _, rfl⟩)
  · have he : θ = 0 := hzero
    rw [he]
    exact Real.pi_pos.le
  · exact angleAt_le_pi w a b

theorem values_bddAbove (Γ : Subgroup SL2) (p w : ℍ) : BddAbove (values Γ p w) :=
  ⟨Real.pi, values_le_pi Γ p w⟩

theorem width_nonneg (Γ : Subgroup SL2) (p w : ℍ) : 0 ≤ width Γ p w :=
  le_csSup (values_bddAbove Γ p w) (Or.inl rfl)

theorem width_le_pi (Γ : Subgroup SL2) (p w : ℍ) : width Γ p w ≤ Real.pi :=
  csSup_le (values_nonempty Γ p w) (values_le_pi Γ p w)

theorem angle_le_width (Γ : Subgroup SL2) (p w a b : ℍ) (ha : a ∈ region Γ p) (hb : b ∈ region Γ p)
    (haw : a ≠ w) (hbw : b ≠ w) : angleAt w a b ≤ width Γ p w :=
  le_csSup (values_bddAbove Γ p w) (Or.inr ⟨a, b, ha, hb, haw, hbw, rfl⟩)

theorem deficit_nonneg (Γ : Subgroup SL2) (p w : ℍ) : 0 ≤ deficit Γ p w :=
  sub_nonneg.mpr (width_le_pi Γ p w)

theorem deficit_le_pi (Γ : Subgroup SL2) (p w : ℍ) : deficit Γ p w ≤ Real.pi := by
  have hn := width_nonneg Γ p w
  unfold deficit
  linarith

theorem deficit_le_corner (Γ : Subgroup SL2) (p w a b : ℍ) (ha : a ∈ region Γ p) (hb : b ∈ region Γ p)
    (haw : a ≠ w) (hbw : b ≠ w) : deficit Γ p w ≤ Real.pi - angleAt w a b := by
  have h := angle_le_width Γ p w a b ha hb haw hbw
  unfold deficit
  linarith

end VeechDichotomy.DirichletCornerAngles
