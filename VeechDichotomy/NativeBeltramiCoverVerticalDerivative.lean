module

public import VeechDichotomy.NativeBeltramiCoverJoint
public import VeechDichotomy.TriangularHolomorphicInverse
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Away from actual cover ramification, the vertical derivative of the
actual joint covering coordinates is nonzero. This is derived from the
native fiber derivative and critical-set preservation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverVerticalDerivative

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCoverCoordinates
open BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} (π : Cover ωX ωY)

theorem vertical_ne_zero (y : Y) (hy : y ∉ criticalSet π) (μ : Parameter) :
    (fderiv ℂ (coordinateMap π y) (μ.val, 0) (0, 1)).2 ≠ 0 := by
  let β := (fderiv ℂ (coordinateMap π y) (μ.val, 0) (0, 1)).2
  have hF := ((NativeBeltramiCoverJoint.coordinate_holomorphic π y μ).differentiableAt (by decide)).hasFDerivAt
  have hin : HasDerivAt (fun z : ℂ => (μ.val, z)) (0, 1) 0 :=
    (hasDerivAt_const 0 μ.val).prodMk (hasDerivAt_id 0)
  have hout : HasFDerivAt (Prod.snd : ℂ × ℂ → ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ)
      (coordinateMap π y (μ.val, 0)) := hasFDerivAt_snd
  have hline := hF.comp_hasDerivAt 0 hin
  have hscalar := hout.comp_hasDerivAt 0 hline
  have hs : HasDerivAt (fun z : ℂ => coordinateScalar π y (μ.val, z)) β 0 :=
    hscalar
  intro hβ
  change β = 0 at hβ
  have hn : mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiCover.cover π μ).map
      (⟨y⟩ : NativeBeltramiSurface.Surface ωY μ) ≠ 0 := by
    intro hzero
    exact hy ((NativeBeltramiCoverBranchValues.critical_iff π μ ⟨y⟩).mp hzero)
  apply hn
  rw [NativeCoverBranchTopology.mfderiv_eq_fderiv_chart]
  change fderiv ℂ (NativeBeltramiSurface.chart ωX μ ⟨π.map y⟩ ∘
    (NativeBeltramiCover.cover π μ).map ∘ (NativeBeltramiSurface.chart ωY μ ⟨y⟩).symm)
    (NativeBeltramiSurface.chart ωY μ ⟨y⟩ ⟨y⟩) = 0
  rw [NativeBeltramiSurface.chart_center_zero]
  have hfun : (NativeBeltramiSurface.chart ωX μ ⟨π.map y⟩ ∘
      (NativeBeltramiCover.cover π μ).map ∘ (NativeBeltramiSurface.chart ωY μ ⟨y⟩).symm) =
      fun z => coordinateScalar π y (μ.val, z) := funext fun z => (slice_value π y μ z).symm
  rw [hfun]
  apply ContinuousLinearMap.ext
  intro z
  rw [fderiv_eq_smul_deriv, hs.deriv, hβ, smul_zero]
  rfl

end VeechDichotomy.NativeBeltramiCoverVerticalDerivative
