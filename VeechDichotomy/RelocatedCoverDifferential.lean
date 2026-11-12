module

public import VeechDichotomy.RelocatedCoverProjection

/-! The actual nonzero holomorphic differential and genuine finite
translation cover on the constructed relocated source curve. Nonvanishing
of the pullback is derived at a regular nonbranch value of the base.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverDifferential

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverAtlas
open Set Filter Topology
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

local instance : ChartedSpace ℂ (Surface π ψ hψ hInv) := RelocatedCoverAtlas.chartedSpace π ψ hψ hInv
local instance : IsManifold 𝓘(ℂ) ω (Surface π ψ hψ hInv) := RelocatedCoverAtlas.isComplexManifold π ψ hψ hInv ω

def differential : Jacobians.HolomorphicOneForms (Surface π ψ hψ hInv) :=
  Jacobians.pullbackForm (RelocatedCoverProjection.map π ψ hψ hInv)
    (RelocatedCoverProjection.holomorphic_map π ψ hψ hInv) ωX.val

theorem differential_ne_zero : differential π ψ hψ hInv ≠ 0 := by
  intro hzero
  have hfin := (zeroSet_finite ωX).union ((branchValues_finite π).image ψ)
  let : Infinite X := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := hfin.exists_notMem
  have hxReg : x ∈ regularSet ωX := fun h => hx (Or.inl h)
  have hxBranch : x ∉ ψ '' branchValues π := fun h => hx (Or.inr h)
  obtain ⟨i, hi⟩ := RelocatedCoverProjection.surjective_map π ψ hψ hInv x
  have hiReg : i.point ∉ criticalSet π := by
    intro hc
    exact hxBranch ⟨π.map i.point, ⟨i.point, hc, rfl⟩, hi⟩
  have hval : (ωX.val.toFun (RelocatedCoverProjection.map π ψ hψ hInv i)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (RelocatedCoverProjection.map π ψ hψ hInv) i) = 0 := by
    have h := congrArg (fun α : Jacobians.HolomorphicOneForms (Surface π ψ hψ hInv) => α.toFun i) hzero
    exact h
  have hBase : ωX.val.toFun (RelocatedCoverProjection.map π ψ hψ hInv i) ≠ 0 := by
    rw [hi]
    exact hxReg
  have hinj := NativeUnramifiedCover.complexLine_injective_of_ne_zero _ hBase
  apply RelocatedCoverProjection.derivative_ne_zero_regular π ψ hψ hInv hiReg
  apply ContinuousLinearMap.ext
  intro z
  apply hinj
  have h := congrArg (fun f : ℂ →L[ℂ] ℂ => f z) hval
  change (ωX.val.toFun (RelocatedCoverProjection.map π ψ hψ hInv i))
    ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (RelocatedCoverProjection.map π ψ hψ hInv) i) z) = 0 at h
  simpa only [zero_apply, map_zero] using! h

def form : Differential (Surface π ψ hψ hInv) := ⟨differential π ψ hψ hInv, differential_ne_zero π ψ hψ hInv⟩

def cover : Cover ωX (form π ψ hψ hInv) where
  map := RelocatedCoverProjection.map π ψ hψ hInv
  holomorphic := RelocatedCoverProjection.holomorphic_map π ψ hψ hInv
  surjective := RelocatedCoverProjection.surjective_map π ψ hψ hInv
  finite_fibers := RelocatedCoverProjection.finite_fibers π ψ hψ hInv
  pullback_eq := rfl

@[simp] theorem cover_map_value (y : Y) :
    (cover π ψ hψ hInv).map ((toOriginal π ψ hψ hInv).symm y) = ψ (π.map y) := rfl

end VeechDichotomy.RelocatedCoverDifferential
