module

public import VeechDichotomy.NativeFiniteCuspCharts

/-! One actual common normalized depth gives a family of genuine
open horoballs whose actual group translates are either identical or
disjoint. The depth also lies above every actual Dirichlet strip cutoff. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCompatibleHoroballs

open LinearGroup Set HyperbolicRegularCenters DirichletIdealRadialPoints NativeFiniteCuspCharts
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def tile (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (R : ℝ) (u : idealBoundary Γ p) (γ : Γ) : Set ℍ :=
  (fun z : ℍ => γ • z) '' RelativeIdealHoroballs.horoball p (chart Γ hΓ p hp u).matrix R

theorem isOpen_tile (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (R : ℝ) (u : idealBoundary Γ p) (γ : Γ) : IsOpen (tile Γ hΓ p hp R u γ) :=
  (Homeomorph.smul γ).isOpenMap _ (RelativeIdealHoroballs.isOpen_horoball p _ R)

theorem tile_eq_or_disjoint (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (R : ℝ) (hR : 0 < R)
    (hdepth : ∀ u : idealBoundary Γ p, let c := chart Γ hΓ p hp u
      c.period ^ 2 + (c.matrix • p).im ^ 2 ≤ R ^ 2 * (c.matrix • p).im ^ 2)
    (u v : idealBoundary Γ p) (γ δ : Γ) :
    tile Γ hΓ p hp R u γ = tile Γ hΓ p hp R v δ ∨
      Disjoint (tile Γ hΓ p hp R u γ) (tile Γ hΓ p hp R v δ) := by
  let B := (chart Γ hΓ p hp u).matrix
  let C := (chart Γ hΓ p hp v).matrix
  let η : Γ := γ⁻¹ * δ
  have hB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p := by
    rw [(chart Γ hΓ p hp u).endpoint_eq]
    exact u.property
  have hC : SL2BottomRowEndpoints.endpoint C ∈ idealBoundary Γ p := by
    rw [(chart Γ hΓ p hp v).endpoint_eq]
    exact v.property
  have hcomp : (fun z : ℍ => γ • z) '' ((fun z : ℍ => η • z) '' RelativeIdealHoroballs.horoball p C R) =
      (fun z : ℍ => δ • z) '' RelativeIdealHoroballs.horoball p C R := by
    rw [image_image]
    have hf : (fun z : ℍ => γ • (η • z)) = fun z : ℍ => δ • z := by
      funext z
      dsimp only [η]
      rw [mul_smul, smul_inv_smul]
    rw [hf]
  rcases RelativeIdealHoroballs.image_eq_or_disjoint Γ p B C hB hC
      (chart Γ hΓ p hp v).period (chart Γ hΓ p hp v).period_pos
      (chart Γ hΓ p hp v).period_mem R hR (hdepth v) η with he | hd
  · have h := congrArg (fun A : Set ℍ => (fun z : ℍ => γ • z) '' A) he
    rw [hcomp] at h
    exact Or.inl h.symm
  · have h := Set.disjoint_image_of_injective (MulAction.injective γ) hd
    rw [hcomp] at h
    exact Or.inr h.symm

theorem exists_compatible_depth (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    ∃ R : ℝ, 0 < R ∧
      (∀ u : idealBoundary Γ p, let c := chart Γ hΓ p hp u
        c.height ≤ R * (c.matrix • p).im) ∧
      (∀ u v : idealBoundary Γ p, ∀ γ δ : Γ,
        tile Γ hΓ p hp R u γ = tile Γ hΓ p hp R v δ ∨
          Disjoint (tile Γ hΓ p hp R u γ) (tile Γ hΓ p hp R v δ)) := by
  obtain ⟨R, hR, hcharts⟩ := exists_common_depth Γ hΓ p hp
  exact ⟨R, hR, fun u => (hcharts u).1,
    fun u v γ δ => tile_eq_or_disjoint Γ hΓ p hp R hR (fun w => (hcharts w).2) u v γ δ⟩

end VeechDichotomy.NativeCompatibleHoroballs
