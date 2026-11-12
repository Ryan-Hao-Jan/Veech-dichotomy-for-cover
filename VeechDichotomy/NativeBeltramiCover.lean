module

public import VeechDichotomy.NativeBeltramiCoverRegular
public import VeechDichotomy.NativePhysicalHolomorphicMap

/-! Every actual finite native translation cover deforms simultaneously
over the complex unit disk, preserving its literal underlying map.
Holomorphicity extends across the source's finite zero set; equality of
the actual holomorphic forms extends from the proved regular pullback.
No cover-existence or form-preservation certificate is supplied. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCover

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCoverRegular
open BeltramiPlane Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (μ : Parameter)

theorem holomorphic_map : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (map π μ) := by
  apply HolomorphicCurveMaps.contMDiff_of_mdifferentiable
  exact MNEC.NativeRemovableMaps.mdifferentiable_of_continuous_off_finite (map π μ) (continuous_map π μ)
    (zeroSet (NativeBeltramiDifferential.form ωY μ)) (zeroSet_finite (NativeBeltramiDifferential.form ωY μ))
    (regular_mdifferentiable π μ)

theorem pullback_eq : Jacobians.pullbackForm (map π μ) (holomorphic_map π μ)
    (NativeBeltramiDifferential.form ωX μ).val = (NativeBeltramiDifferential.form ωY μ).val := by
  apply NativePhysicalHolomorphicMap.form_eq_of_eqOn_regular (NativeBeltramiDifferential.form ωY μ)
  intro y hy
  exact (regular_pullback π μ y hy).symm

def cover : Cover (NativeBeltramiDifferential.form ωX μ) (NativeBeltramiDifferential.form ωY μ) where
  map := map π μ
  holomorphic := holomorphic_map π μ
  surjective x := by
    obtain ⟨y, hy⟩ := π.surjective x.point
    refine ⟨⟨y⟩, ?_⟩
    apply (NativeBeltramiSurface.toOriginal ωX μ).injective
    exact hy
  finite_fibers x := by
    apply ((π.finite_fibers x.point).image (NativeBeltramiSurface.toOriginal ωY μ).symm).subset
    intro y hy
    exact ⟨y.point, congrArg (NativeBeltramiSurface.toOriginal ωX μ) hy, rfl⟩
  pullback_eq := pullback_eq π μ

@[simp] theorem cover_map_point (y : NativeBeltramiSurface.Surface ωY μ) : ((cover π μ).map y).point = π.map y.point := rfl

end VeechDichotomy.NativeBeltramiCover
