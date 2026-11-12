module

public import VeechDichotomy.NativeIdealEndpointParabolic
public import VeechDichotomy.CuspHoroballSeparation
public import VeechDichotomy.ConjugatedHyperbolicActions
public import VeechDichotomy.DirichletUpperStrips

/-! Every actual ideal endpoint has actual parabolic cusp coordinates:
a genuine positive translation period, an exact finite vertical strip
above a finite height, and a high horoball whose group translates can
overlap only under its actual endpoint stabilizer. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeIdealCuspCoordinates

open LinearGroup Set HyperbolicRegularCenters HyperbolicDirichletRegions DirichletIdealRadialPoints
open NativeLatticeConjugation IdealEndpointHeightNormalization ConjugatedHyperbolicActions
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def horoball (B : SL2) (Y : ℝ) : Set ℍ := {z | Y < (B • z).im}

theorem isOpen_horoball (B : SL2) (Y : ℝ) : IsOpen (horoball B Y) := by
  apply isOpen_lt continuous_const
  exact UpperHalfPlane.continuous_im.comp (show Continuous (fun z : ℍ => B • z) by fun_prop)

theorem stabilizer_height (Γ : Subgroup SL2) (p : ℍ) (B : SL2)
    (hu : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p) (γ : Γ)
    (hc : (B * (γ : SL2) * B⁻¹) 1 0 = 0) (z : ℍ) : (B • (γ • z)).im = (B • z).im := by
  have hI := ideal_conjugate Γ p B hu
  have h := CuspHoroballSeparation.stabilizer_height_eq (conjugate Γ B) (B • p) hI
    (toConjugate Γ B γ) hc (B • z)
  rwa [conjugate_smul Γ B γ z] at h

theorem exists_coordinates (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    {u : ℂ} (hu : u ∈ idealBoundary Γ p) :
    ∃ (B : SL2) (τ a b Y : ℝ), SL2BottomRowEndpoints.endpoint B = u ∧ 0 < τ ∧
      IdealInfinityStabilizers.upper τ ∈ conjugate Γ B ∧ a < (B • p).re ∧ (B • p).re < b ∧ 0 < Y ∧
      (∀ z : ℍ, Y ≤ (B • z).im → (z ∈ region Γ p ↔ (B • z).re ∈ Icc a b)) ∧
      (∀ (γ : Γ) (z : ℍ), z ∈ horoball B Y → γ • z ∈ horoball B Y → (B * (γ : SL2) * B⁻¹) 1 0 = 0) := by
  obtain ⟨B, he⟩ := exists_normalizer u hu.2
  have huB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p := by simpa only [he] using hu
  have hI := ideal_conjugate Γ p B huB
  have hΓB := isLattice_conjugate Γ hΓ B
  have hpB := regular_conjugate Γ p hp B
  obtain ⟨τ, hτ, hmem⟩ := CuspHoroballSeparation.exists_positive_period (conjugate Γ B)
    (NativeIdealInfinityParabolic.exists_nonzero_upper (conjugate Γ B) hΓB (B • p) hpB hI)
  obtain ⟨a, b, H, ha, hb, hH, hstrip⟩ := DirichletUpperStrips.exists_upper_strip
    (conjugate Γ B) hΓB (B • p) hpB hI
  let T := CuspHoroballSeparation.threshold (B • p) τ
  let Y := max H T
  have hHY : H ≤ Y := le_max_left _ _
  have hTY : T ≤ Y := le_max_right _ _
  refine ⟨B, τ, a, b, Y, he, hτ, hmem, ha, hb, hH.trans_le hHY, ?_, ?_⟩
  · intro z hz
    exact (mem_region_iff Γ B p z).symm.trans (hstrip (B • z) (hHY.trans hz))
  · intro γ z hz hg
    exact CuspHoroballSeparation.high_overlap_lower_left_zero (conjugate Γ B) (B • p) hI τ hτ hmem
      (toConjugate Γ B γ) (B • z) (hTY.trans_lt hz)
      (by rw [conjugate_smul Γ B γ z]; exact hTY.trans_lt hg)

end VeechDichotomy.NativeIdealCuspCoordinates
