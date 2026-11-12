module

public import VeechDichotomy.NativeConfigurationTransport
public import VeechDichotomy.NativePuncturedCover

/-! Moving the base marks gives actual continuous finite maps on the
original underlying covering surface. Their topological branch values
are the moved marks, and they are holomorphic near the original critical
points. The changed global source complex structure is constructed separately
in RelocatedCoverAtlas; these maps are not holomorphic on the old source globally.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeMovingCoverMap

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeCoverBranchTopology
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

def map (π : Cover ωX ωY) (ψ : X ≃ₜ X) : Y → X := ψ ∘ π.map

theorem continuous_map (π : Cover ωX ωY) (ψ : X ≃ₜ X) : Continuous (map π ψ) :=
  ψ.continuous.comp π.holomorphic.continuous

theorem surjective_map (π : Cover ωX ωY) (ψ : X ≃ₜ X) : Function.Surjective (map π ψ) :=
  ψ.surjective.comp π.surjective

theorem finite_fibers (π : Cover ωX ωY) (ψ : X ≃ₜ X) (x : X) : ((map π ψ) ⁻¹' {x}).Finite := by
  apply (π.finite_fibers (ψ.symm x)).subset
  intro y hy
  change π.map y = ψ.symm x
  apply ψ.injective
  rw [Homeomorph.apply_symm_apply]
  exact hy

theorem proper_map (π : Cover ωX ωY) (ψ : X ≃ₜ X) : IsProperMap (map π ψ) :=
  (continuous_map π ψ).isProperMap

theorem topologicalCriticalSet_eq (π : Cover ωX ωY) (ψ : X ≃ₜ X) :
    Jacobians.Discharge.Manifold.criticalSetGeneral (map π ψ) = criticalSet π := by
  ext y
  change (¬ ∃ U ∈ 𝓝 y, InjOn (map π ψ) U) ↔ y ∈ criticalSet π
  rw [critical_iff_not_locally_injective]
  apply not_congr
  constructor
  · rintro ⟨U, hU, hinj⟩
    exact ⟨U, hU, fun a ha b hb hab => hinj ha hb (congrArg ψ hab)⟩
  · rintro ⟨U, hU, hinj⟩
    exact ⟨U, hU, fun a ha b hb hab => hinj ha hb (ψ.injective hab)⟩

theorem topologicalBranchValues_eq (π : Cover ωX ωY) (ψ : X ≃ₜ X) :
    Jacobians.Discharge.Manifold.criticalValuesGeneral (map π ψ) = ψ '' branchValues π := by
  change (ψ ∘ π.map) '' Jacobians.Discharge.Manifold.criticalSetGeneral (map π ψ) = _
  rw [topologicalCriticalSet_eq]
  exact (image_image ψ π.map (criticalSet π)).symm

theorem branch_tuple (π : Cover ωX ωY) (ψ : X ≃ₜ X) {m : ℕ} (b : Fin m → X)
    (hb : range b = branchValues π) :
    Jacobians.Discharge.Manifold.criticalValuesGeneral (map π ψ) = range (fun i => ψ (b i)) := by
  rw [topologicalBranchValues_eq, ← hb, ← range_comp]
  rfl

theorem localHomeomorph_noncritical (π : Cover ωX ωY) (ψ : X ≃ₜ X) :
    IsLocalHomeomorphOn (map π ψ) (criticalSet π)ᶜ :=
  ψ.isLocalHomeomorph.isLocalHomeomorphOn.comp
    (NativePuncturedCover.isLocalHomeomorphOn_noncritical π) (fun _ _ => mem_univ _)

theorem holomorphic_near_critical (π : Cover ωX ωY) (ψ : X ≃ₜ X)
    (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
    {y : Y} (hy : y ∈ criticalSet π) :
    ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π ψ) z := by
  have hnear := π.holomorphic.continuous.continuousAt (hψ (π.map y) ⟨y, hy, rfl⟩)
  filter_upwards [hnear] with z hz
  exact hz.comp z (π.holomorphic.mdifferentiableAt (by decide))

theorem continuous_family {P : Type*} [TopologicalSpace P] (π : Cover ωX ωY)
    (ψ : P → X ≃ₜ X) (hψ : Continuous (fun p : P × X => ψ p.1 p.2)) :
    Continuous (fun p : P × Y => map π (ψ p.1) p.2) :=
  hψ.comp (continuous_fst.prodMk (π.holomorphic.continuous.comp continuous_snd))

end VeechDichotomy.NativeMovingCoverMap
