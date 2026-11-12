module

public import VeechDichotomy.RelocatedCoverDifferential

/-! Where the moved projection is old-holomorphic and retains its critical
points, the old and relocated source complex structures agree locally.
Both directions of the actual topology identity are proved holomorphic. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverLocalIdentity

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open RelocatedCoverTransitions RelocatedCoverAtlas Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)
variable {U : Set Y} (hU : IsOpen U)
  (hAnalytic : ∀ z ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z ∧
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z = 0 ↔ z ∈ criticalSet π))

include hU hAnalytic

theorem rawChart_old_differentiable {y : Y} (hy : y ∈ U) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (rawChart π ψ hψ hInv y) y ∧
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (rawChart π ψ hψ hInv y).symm (rawChart π ψ hψ hInv y y) := by
  by_cases hc : y ∈ criticalSet π
  · rw [rawChart_critical π ψ hψ hInv hc]
    have h := criticalChart_mdifferentiable π ψ hψ hInv ⟨y, hc⟩
    have hs := criticalChart_center π ψ hψ hInv ⟨y, hc⟩
    exact ⟨h.mdifferentiableAt hs, h.mdifferentiableAt_symm ((criticalChart π ψ hψ hInv ⟨y, hc⟩).map_source hs)⟩
  · rw [rawChart_regular π ψ hψ hInv hc]
    let f := (localMap π ψ ⟨y, hc⟩).restr U
    have hf : f.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
      apply NativeMovingCoverRegularity.local_chart_holomorphic π ψ f
      · exact fun z _ => localMap_apply π ψ ⟨y, hc⟩ z
      · exact fun z hz => (hAnalytic z (interior_subset hz.2)).1
      · intro z hz hzero
        exact localMap_source_noncritical π ψ ⟨y, hc⟩ hz.1 ((hAnalytic z (interior_subset hz.2)).2.mp hzero)
    have hs : y ∈ f.source := ⟨localMap_center π ψ ⟨y, hc⟩, by rw [hU.interior_eq]; exact hy⟩
    let g := f.trans (baseChart π ψ ⟨y, hc⟩)
    have hg : g.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := hf.trans (mdifferentiable_chart (projection π ψ y))
    have hgs : y ∈ g.source := ⟨hs, (regularChart_center π ψ ⟨y, hc⟩).2⟩
    exact ⟨hg.mdifferentiableAt hgs, hg.mdifferentiableAt_symm (g.map_source hgs)⟩

theorem toOriginal_mdifferentiableAt {i : Surface π ψ hψ hInv} (hi : i.point ∈ U) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toOriginal π ψ hψ hInv) i := by
  have hOld := rawChart_old_differentiable π ψ hψ hInv hU hAnalytic hi
  have hNew : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i) i :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i) (mem_chart_source ℂ i)
  apply (hOld.2.comp i hNew).congr_of_eventuallyEq
  filter_upwards [(chart π ψ hψ hInv i).open_source.mem_nhds (chart_center π ψ hψ hInv i)] with z hz
  exact ((rawChart π ψ hψ hInv i.point).left_inv hz).symm

theorem fromOriginal_mdifferentiableAt {i : Surface π ψ hψ hInv} (hi : i.point ∈ U) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toOriginal π ψ hψ hInv).symm i.point := by
  have hOld := rawChart_old_differentiable π ψ hψ hInv hU hAnalytic hi
  have hs := chart_center π ψ hψ hInv i
  have hNew : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i).symm (chart π ψ hψ hInv i i) :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i) ((chart π ψ hψ hInv i).map_source hs)
  apply (hNew.comp i.point hOld.1).congr_of_eventuallyEq
  filter_upwards [(rawChart π ψ hψ hInv i.point).open_source.mem_nhds
    (rawChart_center π ψ hψ hInv i.point)] with z hz
  apply (toOriginal π ψ hψ hInv).injective
  exact ((rawChart π ψ hψ hInv i.point).left_inv hz).symm

end VeechDichotomy.RelocatedCoverLocalIdentity
