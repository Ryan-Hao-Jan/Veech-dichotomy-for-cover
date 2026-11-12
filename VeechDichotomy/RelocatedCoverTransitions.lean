module

public import VeechDichotomy.RelocatedCoverCharts

/-! Holomorphic compatibility of the constructed relocated-cover charts.
Regular overlaps reduce to base atlas transitions. Mixed overlaps use
the actual native analytic neighborhoods and proved inverse calculus.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverTransitions

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open Set Filter Topology
open scoped Manifold ContDiff Classical

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

theorem regular_regular_differentiableAt (π : Cover ωX ωY) (ψ : X ≃ₜ X)
    (i j : RegularPoint π) (z : ℂ)
    (hz : z ∈ ((regularChart π ψ i).symm.trans (regularChart π ψ j)).source) :
    DifferentiableAt ℂ ((regularChart π ψ i).symm.trans (regularChart π ψ j)) z := by
  have hj : projection π ψ ((regularChart π ψ i).symm z) ∈ (baseChart π ψ j).source := by
    have h := hz.2.2
    change localMap π ψ j ((regularChart π ψ i).symm z) ∈ (baseChart π ψ j).source at h
    rwa [localMap_apply] at h
  rw [regularChart_inverse_projection π ψ i hz.1] at hj
  have hA := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ))
    (chart_mem_atlas ℂ (projection π ψ i.val)) hz.1.1
  have hB := mdifferentiableAt_atlas (I := 𝓘(ℂ))
    (chart_mem_atlas ℂ (projection π ψ j.val)) hj
  have htarget := ComplexAtlasTools.transition_differentiableAt (baseChart π ψ i) (baseChart π ψ j) z hA hB
  have heq : ((regularChart π ψ i).symm.trans (regularChart π ψ j) : ℂ → ℂ) =ᶠ[𝓝 z]
      ((baseChart π ψ i).symm.trans (baseChart π ψ j)) := by
    filter_upwards [(regularChart π ψ i).open_target.mem_nhds hz.1] with w hw
    change regularChart π ψ j ((regularChart π ψ i).symm w) = baseChart π ψ j ((baseChart π ψ i).symm w)
    rw [regularChart_apply, regularChart_inverse_projection π ψ i hw]
  exact htarget.congr_of_eventuallyEq heq

variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

def rawChart (y : Y) : OpenPartialHomeomorph Y ℂ :=
  if hy : y ∈ criticalSet π then criticalChart π ψ hψ hInv ⟨y, hy⟩ else regularChart π ψ ⟨y, hy⟩

theorem rawChart_critical {y : Y} (hy : y ∈ criticalSet π) :
    rawChart π ψ hψ hInv y = criticalChart π ψ hψ hInv ⟨y, hy⟩ := by
  rw [rawChart, dite_eq_left hy]

theorem rawChart_regular {y : Y} (hy : y ∉ criticalSet π) :
    rawChart π ψ hψ hInv y = regularChart π ψ ⟨y, hy⟩ := by
  rw [rawChart, dite_eq_right hy]

theorem rawChart_center (y : Y) : y ∈ (rawChart π ψ hψ hInv y).source := by
  by_cases hy : y ∈ criticalSet π
  · rw [rawChart_critical π ψ hψ hInv hy]
    exact criticalChart_center π ψ hψ hInv ⟨y, hy⟩
  · rw [rawChart_regular π ψ hψ hInv hy]
    exact regularChart_center π ψ ⟨y, hy⟩

theorem raw_transition_differentiableAt (i j : Y) (z : ℂ)
    (hz : z ∈ ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j)).source) :
    DifferentiableAt ℂ ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j)) z := by
  by_cases hi : i ∈ criticalSet π
  · rw [rawChart_critical π ψ hψ hInv hi] at hz ⊢
    by_cases hj : j ∈ criticalSet π
    · rw [rawChart_critical π ψ hψ hInv hj] at hz ⊢
      exact ComplexAtlasTools.transition_differentiableAt _ _ z
        ((criticalChart_mdifferentiable π ψ hψ hInv ⟨i, hi⟩).mdifferentiableAt_symm hz.1)
        ((criticalChart_mdifferentiable π ψ hψ hInv ⟨j, hj⟩).mdifferentiableAt hz.2)
    · rw [rawChart_regular π ψ hψ hInv hj] at hz ⊢
      have hx := (criticalChart π ψ hψ hInv ⟨i, hi⟩).map_target hz.1
      have hreg := regularChart_old_differentiable π ψ hψ hInv ⟨j, hj⟩ ⟨i, hi⟩ hz.2 (interior_subset hx.2)
      exact ComplexAtlasTools.transition_differentiableAt _ _ z
        ((criticalChart_mdifferentiable π ψ hψ hInv ⟨i, hi⟩).mdifferentiableAt_symm hz.1) hreg.1
  · rw [rawChart_regular π ψ hψ hInv hi] at hz ⊢
    by_cases hj : j ∈ criticalSet π
    · rw [rawChart_critical π ψ hψ hInv hj] at hz ⊢
      have hx := (regularChart π ψ ⟨i, hi⟩).map_target hz.1
      have hreg := regularChart_old_differentiable π ψ hψ hInv ⟨i, hi⟩ ⟨j, hj⟩ hx (interior_subset hz.2.2)
      have hinverse : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (regularChart π ψ ⟨i, hi⟩).symm z := by
        have h := hreg.2
        rwa [(regularChart π ψ ⟨i, hi⟩).right_inv hz.1] at h
      exact ComplexAtlasTools.transition_differentiableAt _ _ z hinverse
        ((criticalChart_mdifferentiable π ψ hψ hInv ⟨j, hj⟩).mdifferentiableAt hz.2)
    · rw [rawChart_regular π ψ hψ hInv hj] at hz ⊢
      exact regular_regular_differentiableAt π ψ ⟨i, hi⟩ ⟨j, hj⟩ z hz

theorem raw_transition_contDiffOn (n : ℕ∞ω) (i j : Y) :
    ContDiffOn ℂ n ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j))
      ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j)).source := by
  have hd : DifferentiableOn ℂ ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j))
      ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j)).source :=
    fun z hz => (raw_transition_differentiableAt π ψ hψ hInv i j z hz).differentiableWithinAt
  exact hd.contDiffOn ((rawChart π ψ hψ hInv i).symm.trans (rawChart π ψ hψ hInv j)).open_source

end VeechDichotomy.RelocatedCoverTransitions
