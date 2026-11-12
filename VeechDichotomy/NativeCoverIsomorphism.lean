module

public import VeechDichotomy.NativeRelativePuncturedCover
public import MNEC.NativeDifferentialEquivCompletion

/-! A whole-curve homeomorphism commuting with two genuine finite
translation covers is automatically a genuine holomorphic differential
equivalence. Holomorphicity is obtained from local inverses off finite
branch fibers and the proved removable-point theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverIsomorphism

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeCoverBranchTopology
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {ωX : Differential X} {ωY : Differential Y} {ωZ : Differential Z}

theorem mdifferentiableAt_of_commutes (π : Cover ωX ωY) (ρ : Cover ωX ωZ)
    (H : Y → Z) (hH : Continuous H) (hsquare : ∀ y, ρ.map (H y) = π.map y)
    (y : Y) (hy : π.map y ∉ branchValues ρ) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H y := by
  have hz : H y ∉ criticalSet ρ := fun h => hy ⟨H y, h, hsquare y⟩
  have hder : deriv ((chartAt ℂ (ρ.map (H y))) ∘ ρ.map ∘ (chartAt ℂ (H y)).symm)
      ((chartAt ℂ (H y)) (H y)) ≠ 0 := by
    intro heq
    apply hz
    change mfderiv 𝓘(ℂ) 𝓘(ℂ) ρ.map (H y) = 0
    rw [mfderiv_eq_fderiv_chart]
    apply ContinuousLinearMap.ext
    intro z
    simp only [fderiv_eq_smul_deriv, heq, smul_zero, zero_apply]
  obtain ⟨g, V, hV, hzV, hgcenter, hgsection, hgHol⟩ :=
    Jacobians.exists_holo_localInverse ρ.map ρ.holomorphic (H y) hder
  have hyV : π.map y ∈ V := by rwa [hsquare] at hzV
  have hgcenter' : g (π.map y) = H y := by rwa [hsquare] at hgcenter
  have hgDiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (π.map y) :=
    (hgHol.mdifferentiableOn (by decide)).mdifferentiableAt (hV.mem_nhds hyV)
  have hcomp := hgDiff.comp y (π.holomorphic.mdifferentiableAt (by decide))
  have hinj : ∃ U ∈ 𝓝 (H y), InjOn ρ.map U := by
    by_contra hn
    exact hz ((critical_iff_not_locally_injective ρ (H y)).mpr hn)
  obtain ⟨U, hU, hρU⟩ := hinj
  have hnearG : ∀ᶠ z in 𝓝 y, g (π.map z) ∈ U := by
    have hu' : U ∈ 𝓝 (g (π.map y)) := by rw [hgcenter']; exact hU
    exact hcomp.continuousAt hu'
  have hfactor : H =ᶠ[𝓝 y] g ∘ π.map := by
    filter_upwards [hH.continuousAt hU, hnearG,
      π.holomorphic.continuous.continuousAt (hV.mem_nhds hyV)] with z hzH hzG hzV'
    apply hρU hzH hzG
    exact (hsquare z).trans (hgsection (π.map z) hzV').symm
  exact hcomp.congr_of_eventuallyEq hfactor

theorem mdifferentiable_of_commutes (π : Cover ωX ωY) (ρ : Cover ωX ωZ)
    (H : Y → Z) (hH : Continuous H) (hsquare : ∀ y, ρ.map (H y) = π.map y) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := by
  apply MNEC.NativeRemovableMaps.mdifferentiable_of_continuous_off_finite H hH
    (π.map ⁻¹' branchValues ρ) (NativeRelativePuncturedCover.preimage_finite π (branchValues_finite ρ))
  exact fun y hy => mdifferentiableAt_of_commutes π ρ H hH hsquare y hy

def equivalence_of_commutes (π : Cover ωX ωY) (ρ : Cover ωX ωZ)
    (H : Y ≃ₜ Z) (hsquare : ∀ y, ρ.map (H y) = π.map y) :
    MNEC.NativeDifferentialEquiv.Equiv ωY ωZ where
  homeomorph := H
  differentiable := mdifferentiable_of_commutes π ρ H H.continuous hsquare
  inverse_differentiable := mdifferentiable_of_commutes ρ π H.symm H.symm.continuous (by
    intro z
    simpa only [Homeomorph.apply_symm_apply] using (hsquare (H.symm z)).symm)
  oneForm_pullback y := by
    have hHD := (mdifferentiable_of_commutes π ρ H H.continuous hsquare y).hasMFDerivAt
    have hcomp := (ρ.holomorphic.mdifferentiableAt (by decide) (x := H y)).hasMFDerivAt.comp y hHD
    have hd : mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y =
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) ρ.map (H y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H y) := by
      have h := hcomp.congr_of_eventuallyEq_abuse (Filter.Eventually.of_forall fun z => (hsquare z).symm)
      exact h.mfderiv
    rw [pullback_at π y, pullback_at ρ (H y), hsquare y, ContinuousLinearMap.comp_assoc, hd]

end VeechDichotomy.NativeCoverIsomorphism
