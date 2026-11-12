module

public import VeechDichotomy.NonzeroComplexParameter
public import VeechDichotomy.NativeBeltramiRelativeForm

/-! The genuine analytic disk family extended by a nonzero complex
scalar. The parameter projection is proper and holomorphic; fibers carry
the actual scalar-rescaled native differentials, with joint holomorphic
relative coefficient functions and holomorphic fiber inclusions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeScaledBeltramiFamily

open MNEC.NativeAbelianDifferential Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

abbrev Base := NonzeroComplexParameter.Parameter × BeltramiPlane.Parameter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

abbrev Total := NonzeroComplexParameter.Parameter × NativeBeltramiTotalSpace.TotalSpace q

def projection (z : Total q) : Base := (z.1, NativeBeltramiTotalSpace.projection q z.2)

theorem proper_projection : IsProperMap (projection q) :=
  isProperMap_id.prodMap (NativeBeltramiTotalSpace.proper_projection q)

theorem projection_holomorphic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (projection q) :=
  contMDiff_id.prodMap (NativeBeltramiTotalSpace.projection_holomorphic q)

def fiberForm (p : Base) : Differential (NativeBeltramiSurface.Surface q p.2) :=
  ⟨p.1.val • (NativeBeltramiDifferential.form q p.2).val,
    smul_ne_zero p.1.property (NativeBeltramiDifferential.differential_ne_zero q p.2)⟩

def inclusion (p : Base) (x : NativeBeltramiSurface.Surface q p.2) : Total q :=
  (p.1, NativeBeltramiFibers.inclusion q p.2 x)

theorem projection_inclusion (p : Base) (x : NativeBeltramiSurface.Surface q p.2) :
    projection q (inclusion q p x) = p := rfl

theorem holomorphic_inclusion (p : Base) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) ω (inclusion q p) :=
  contMDiff_const.prodMk (NativeBeltramiFibers.holomorphic_inclusion q p.2)

def fiberHomeomorph (p : Base) : NativeBeltramiSurface.Surface q p.2 ≃ₜ (projection q ⁻¹' {p}) where
  toFun x := ⟨inclusion q p x, rfl⟩
  invFun z := (NativeBeltramiSurface.toOriginal q p.2).symm z.val.2.point.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact (congrArg Prod.fst z.property).symm
    · apply (NativeBeltramiTotalSpace.toProduct q).injective
      exact Prod.ext (congrArg Prod.snd z.property).symm rfl
  continuous_toFun := (continuous_const.prodMk (NativeBeltramiFibers.continuous_inclusion q p.2)).subtype_mk _
  continuous_invFun := (NativeBeltramiSurface.toOriginal q p.2).symm.continuous.comp
    (continuous_snd.comp ((NativeBeltramiTotalSpace.toProduct q).continuous.comp (continuous_snd.comp continuous_subtype_val)))

def coefficient (i : X) (p : ℂ × (ℂ × ℂ)) : ℂ := p.1 * NativeBeltramiRelativeForm.coefficient q i p.2

theorem coefficient_holomorphic (i : X) : ContDiff ℂ ω (coefficient q i) :=
  contDiff_fst.mul ((NativeBeltramiRelativeForm.coefficient_holomorphic q i).comp contDiff_snd)

theorem fiber_coefficient (p : Base) (i y : NativeBeltramiSurface.Surface q p.2)
    (hy : y ∈ (NativeBeltramiSurface.chart q p.2 i).source) :
    Jacobians.Montel.localRep (fiberForm q p).val i y =
      coefficient q i.point (p.1.val, NativeBeltramiCharts.chart q i.point (p.2, y.point)) :=
  congrArg (fun z : ℂ => p.1.val * z) (NativeBeltramiRelativeForm.fiber_coefficient q p.2 i y hy)

theorem continuousOn_product (i : X) :
    ContinuousOn (fun p : NonzeroComplexParameter.Parameter × (BeltramiPlane.Parameter × X) =>
      p.1.val * NativeBeltramiRelativeForm.coefficient q i (NativeBeltramiCharts.chart q i p.2))
      (Prod.snd ⁻¹' (NativeBeltramiCharts.chart q i).source) :=
  (continuous_subtype_val.comp continuous_fst).continuousOn.mul
    ((NativeBeltramiRelativeForm.continuousOn_product q i).comp continuous_snd.continuousOn (fun _ hp => hp))

end VeechDichotomy.NativeScaledBeltramiFamily
