module

public import VeechDichotomy.NativeBeltramiDifferential

/-! Actual native unit-disk curves identify with the proper family's
fibers, and their inclusions are holomorphic. Total and fiber coordinates
agree literally, so the analytic family has the intended source curves. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiFibers

open MNEC.NativeAbelianDifferential BeltramiPlane NativeBeltramiSurface Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (μ : Parameter)

def fiberHomeomorph : Surface q μ ≃ₜ (NativeBeltramiTotalSpace.projection q ⁻¹' {μ}) where
  toFun x := ⟨⟨(μ, x.point)⟩, rfl⟩
  invFun x := (toOriginal q μ).symm x.val.point.2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply (NativeBeltramiTotalSpace.toProduct q).injective
    exact Prod.ext x.property.symm rfl
  continuous_toFun := ((NativeBeltramiTotalSpace.toProduct q).symm.continuous.comp
    (continuous_const.prodMk (toOriginal q μ).continuous)).subtype_mk _
  continuous_invFun := (toOriginal q μ).symm.continuous.comp
    (continuous_snd.comp ((NativeBeltramiTotalSpace.toProduct q).continuous.comp continuous_subtype_val))

def inclusion (x : Surface q μ) : NativeBeltramiTotalSpace.TotalSpace q := (fiberHomeomorph q μ x).val

theorem continuous_inclusion : Continuous (inclusion q μ) := continuous_subtype_val.comp (fiberHomeomorph q μ).continuous

theorem chart_inclusion (i y : Surface q μ) :
    NativeBeltramiTotalSpace.chart q (inclusion q μ i) (inclusion q μ y) = (μ.val, chart q μ i y) := rfl

theorem holomorphic_inclusion : ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω (inclusion q μ) := by
  intro x
  rw [contMDiffAt_iff_target_of_mem_source (y := inclusion q μ x) (mem_chart_source (ℂ × ℂ) (inclusion q μ x))]
  refine ⟨(continuous_inclusion q μ).continuousAt, ?_⟩
  have heq : (extChartAt 𝓘(ℂ, ℂ × ℂ) (inclusion q μ x) ∘ inclusion q μ) =
      fun y => (μ.val, chart q μ x y) := by
    funext y
    exact chart_inclusion q μ x y
  rw [heq]
  have hconst : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : Surface q μ => μ.val) x := contMDiffAt_const
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chart q μ x) x :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (x := x)).contMDiffAt ((chart q μ x).open_source.mem_nhds (chart_center q μ x))
  exact hconst.prodMk_space hchart

end VeechDichotomy.NativeBeltramiFibers
