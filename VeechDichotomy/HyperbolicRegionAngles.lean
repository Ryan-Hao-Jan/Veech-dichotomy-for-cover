module

public import VeechDichotomy.DirichletInteriorDensity

/-! Actual angular widths for arbitrary hyperbolic regions and actual
complex direction sets. Genuine SL2 angle invariance transports the entire
point-angle set, hence its actual supremum. The Dirichlet specialization
is literally the existing deficit-budget angle definition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicRegionAngles

open LinearGroup Set HyperbolicIntrinsicAngles HyperbolicDirichletRegions HyperbolicDirichletTessellation
open scoped UpperHalfPlane

def pointValues (S : Set ℍ) (w : ℍ) : Set ℝ := {0} ∪
  {θ | ∃ a b : ℍ, a ∈ S ∧ b ∈ S ∧ a ≠ w ∧ b ≠ w ∧ θ = angleAt w a b}

def pointWidth (S : Set ℍ) (w : ℍ) : ℝ := sSup (pointValues S w)

def vectorValues (K : Set ℂ) : Set ℝ := {0} ∪
  {θ | ∃ u v : ℂ, u ∈ K ∧ v ∈ K ∧ u ≠ 0 ∧ v ≠ 0 ∧ θ = InnerProductGeometry.angle u v}

def vectorWidth (K : Set ℂ) : ℝ := sSup (vectorValues K)

theorem vectorValues_nonempty (K : Set ℂ) : (vectorValues K).Nonempty := ⟨0, Or.inl rfl⟩

theorem vectorValues_le_pi (K : Set ℂ) : ∀ θ ∈ vectorValues K, θ ≤ Real.pi := by
  rintro θ (hz | ⟨u, v, _, _, _, _, rfl⟩)
  · have he : θ = 0 := hz
    rw [he]
    exact Real.pi_pos.le
  · exact InnerProductGeometry.angle_le_pi u v

theorem vectorValues_bddAbove (K : Set ℂ) : BddAbove (vectorValues K) := ⟨Real.pi, vectorValues_le_pi K⟩

theorem vectorWidth_nonneg (K : Set ℂ) : 0 ≤ vectorWidth K :=
  le_csSup (vectorValues_bddAbove K) (Or.inl rfl)

theorem vectorWidth_le_pi (K : Set ℂ) : vectorWidth K ≤ Real.pi :=
  csSup_le (vectorValues_nonempty K) (vectorValues_le_pi K)

theorem pointValues_smul (A : SL2) (S : Set ℍ) (w : ℍ) :
    pointValues ((fun z : ℍ => A • z) '' S) (A • w) = pointValues S w := by
  ext θ
  constructor
  · rintro (hz | ⟨a', b', ha, hb, haw, hbw, hθ⟩)
    · exact Or.inl hz
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      refine Or.inr ⟨a, b, ha, hb, ?_, ?_, ?_⟩
      · exact fun he => haw (congrArg (fun z : ℍ => A • z) he)
      · exact fun he => hbw (congrArg (fun z : ℍ => A • z) he)
      · simpa only [angleAt_smul] using hθ
  · rintro (hz | ⟨a, b, ha, hb, haw, hbw, hθ⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨A • a, A • b, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_, ?_, ?_⟩
      · exact fun he => haw (MulAction.injective A he)
      · exact fun he => hbw (MulAction.injective A he)
      · rwa [angleAt_smul]

theorem pointWidth_smul (A : SL2) (S : Set ℍ) (w : ℍ) :
    pointWidth ((fun z : ℍ => A • z) '' S) (A • w) = pointWidth S w := by
  unfold pointWidth
  rw [pointValues_smul]

theorem dirichlet_width (Γ : Subgroup SL2) (p w : ℍ) :
    pointWidth (region Γ p) w = DirichletCornerAngles.width Γ p w := rfl

theorem tile_width (Γ : Subgroup SL2) (p w : ℍ) (γ : Γ) :
    pointWidth (tile Γ p γ) (γ • w) = DirichletCornerAngles.width Γ p w := by
  exact pointWidth_smul (γ : SL2) (region Γ p) w

end VeechDichotomy.HyperbolicRegionAngles
