module

public import VeechDichotomy.NativeMovingCoverMap
public import VeechDichotomy.HolomorphicLocalInverse

/-! Analytic control needed to attach the critical-point neighborhoods
to a moved cover's pulled-back regular atlas. Near old critical fibers,
the moved map is holomorphic and has exactly the old critical points.
Actual regular chart inverses are then proved holomorphic. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeMovingCoverRegularity

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeMovingCoverMap
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y] in
theorem homeomorph_derivative_ne_zero (ψ : X ≃ₜ X) (x : X)
    (hψ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
    (hInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm (ψ x)) : mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ x ≠ 0 := by
  intro hz
  have h := hInv.hasMFDerivAt.comp x hψ.hasMFDerivAt
  rw [hz, ContinuousLinearMap.comp_zero] at h
  have hId : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) id x (0 : ℂ →L[ℂ] ℂ) :=
    h.congr_of_eventuallyEq_abuse (Filter.Eventually.of_forall fun z => (ψ.symm_apply_apply z).symm)
  have heq : ContinuousLinearMap.id ℂ ℂ = 0 := by simpa only [mfderiv_id] using! hId.mfderiv
  have h1 := congrArg (fun f : ℂ →L[ℂ] ℂ => f 1) heq
  exact one_ne_zero (by simpa only [ContinuousLinearMap.id_apply, zero_apply] using h1)

theorem derivative_zero_iff (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : Y)
    (hψ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (π.map y))
    (hInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm (ψ (π.map y))) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ) y = 0 ↔ y ∈ criticalSet π := by
  have hcomp := hψ.hasMFDerivAt.comp y (π.holomorphic.mdifferentiableAt (by decide)).hasMFDerivAt
  have hd : mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ) y =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (π.map y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y) := hcomp.mfderiv
  have hinj := NativeUnramifiedCover.complexLine_injective_of_ne_zero _
    (homeomorph_derivative_ne_zero ψ (π.map y) hψ hInv)
  change _ ↔ mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y = 0
  rw [hd]
  constructor
  · intro hz
    apply ContinuousLinearMap.ext
    intro z
    apply hinj
    have h := congrArg (fun f : ℂ →L[ℂ] ℂ => f z) hz
    change (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (π.map y)) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y) z) = 0 at h
    simpa only [zero_apply, map_zero] using! h
  · intro hz
    rw [hz, ContinuousLinearMap.comp_zero]

theorem analytic_near_critical (π : Cover ωX ωY) (ψ : X ≃ₜ X)
    (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
    (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)
    {y : Y} (hy : y ∈ criticalSet π) :
    ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π ψ) z ∧
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ) z = 0 ↔ z ∈ criticalSet π) := by
  have hb : π.map y ∈ branchValues π := ⟨y, hy, rfl⟩
  have hfor := π.holomorphic.continuous.continuousAt (hψ (π.map y) hb)
  have hback := (continuous_map π ψ).continuousAt (hInv (π.map y) hb)
  filter_upwards [hfor, hback] with z hz hzInv
  exact ⟨hz.comp z (π.holomorphic.mdifferentiableAt (by decide)), derivative_zero_iff π ψ z hz hzInv⟩

theorem local_chart_holomorphic (π : Cover ωX ωY) (ψ : X ≃ₜ X)
    (e : OpenPartialHomeomorph Y X) (hmap : ∀ y ∈ e.source, e y = map π ψ y)
    (hHol : ∀ y ∈ e.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π ψ) y)
    (hder : ∀ y ∈ e.source, mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ) y ≠ 0) :
    e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  have hnear (y : Y) (hy : y ∈ e.source) : (e : Y → X) =ᶠ[𝓝 y] map π ψ := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    exact hmap z hz
  apply HolomorphicLocalInverse.mdifferentiable e
  · exact fun y hy => (hHol y hy).congr_of_eventuallyEq (hnear y hy)
  · intro y hy hz
    have h := (hHol y hy).hasMFDerivAt.congr_of_eventuallyEq_abuse (hnear y hy)
    exact hder y hy (h.mfderiv.symm.trans hz)

end VeechDichotomy.NativeMovingCoverRegularity
