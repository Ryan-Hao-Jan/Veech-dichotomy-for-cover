module

public import VeechDichotomy.NativePhysicalHolomorphicMap
public import VeechDichotomy.NativeTranslationCover
public import Jacobians.MappingDegree.CriticalValuesFiniteGeneral

/-! Critical points of a genuine finite native translation cover are
exactly the points with no injective neighborhood. This identifies the
analytic branch values with the topology of the actual map. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverBranchTopology

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

theorem not_constant (π : Cover ωX ωY) : ¬ Jacobians.Discharge.IsConstantMap π.map := by
  rintro ⟨x, hx⟩
  let : Nontrivial X := NativePhysicalHolomorphicMap.nontrivial ωX
  obtain ⟨z, hzx⟩ := exists_ne x
  obtain ⟨y, hy⟩ := π.surjective z
  exact hzx (hy.symm.trans (hx y))

theorem mfderiv_eq_fderiv_chart (π : Cover ωX ωY) (y : Y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y =
      fderiv ℂ ((chartAt ℂ (π.map y)) ∘ π.map ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) := by
  rw [(π.holomorphic.mdifferentiableAt (by decide) (x := y)).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ]

theorem critical_iff_not_locally_injective (π : Cover ωX ωY) (y : Y) :
    y ∈ criticalSet π ↔ ¬ ∃ U ∈ 𝓝 y, InjOn π.map U := by
  let D := Jacobians.Discharge.Manifold.criticalChartPullbackData_general
    π.map π.holomorphic (not_constant π) y
  have h := D.hCompat ⟨y, D.hxV⟩
  change (¬ ∃ U ∈ 𝓝 y, InjOn π.map U) ↔
    deriv ((chartAt ℂ (π.map y)) ∘ π.map ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = 0 at h
  rw [h]
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y = 0 ↔ _
  rw [mfderiv_eq_fderiv_chart]
  constructor
  · intro hz
    have hp := congrArg (fun f : ℂ →L[ℂ] ℂ => f 1) hz
    simpa only [fderiv_eq_smul_deriv, one_smul, zero_apply] using hp
  · intro hz
    apply ContinuousLinearMap.ext
    intro z
    simp only [fderiv_eq_smul_deriv, hz, smul_zero, zero_apply]

end VeechDichotomy.NativeCoverBranchTopology
