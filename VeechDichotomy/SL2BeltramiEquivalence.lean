module

public import VeechDichotomy.SL2BeltramiComparisonCharts
public import VeechDichotomy.HolomorphicScalarChartMap
public import MNEC.NativeDifferentialEquivCompletion

/-! The constructed native SL2 differential is genuinely equivalent to
the scalar-rescaled analytic unit-disk fiber differential. The whole map
is the underlying-point identity; regular holomorphicity and cotangent
pullback are derived from the actual scalar chart formula, and the proved
finite-zero completion extends the comparison across every zero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2BeltramiEquivalence

open MNEC.NativeAbelianDifferential LinearGroup SL2BeltramiParameters
open SL2BeltramiComparisonCharts Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

theorem forward_mdifferentiable (x : WholeDeformedAtlas.WholeSurface q A)
    (hx : x ∈ regularSet (WholeDeformedDifferential.form q A)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toBeltrami q A) x :=
  HolomorphicScalarChartMap.mdifferentiableAt (toBeltrami q A) (toBeltrami q A).continuous
    (WholeDeformedAtlas.chart q A x) (NativeBeltramiSurface.chart q (parameter A) (toBeltrami q A x))
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x))
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (toBeltrami q A x)))
    (WholeDeformedAtlas.chart_center q A x) (NativeBeltramiSurface.chart_center q (parameter A) (toBeltrami q A x))
    (scalar_ne_zero A)
    (Filter.Eventually.of_forall (chart_scalar_relation q A x ((source_regular_iff q A x).mp hx)))

theorem inverse_mdifferentiable (y : NativeBeltramiSurface.Surface q (parameter A))
    (hy : y ∈ regularSet (scaledForm q A)) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (toBeltrami q A).symm y := by
  let x := (toBeltrami q A).symm y
  have hx : x.point ∈ regularSet q := (target_regular_iff q A y).mp hy
  refine HolomorphicScalarChartMap.mdifferentiableAt (toBeltrami q A).symm (toBeltrami q A).symm.continuous
    (NativeBeltramiSurface.chart q (parameter A) y) (WholeDeformedAtlas.chart q A x)
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ y))
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x))
    (NativeBeltramiSurface.chart_center q (parameter A) y) (WholeDeformedAtlas.chart_center q A x)
    (inv_ne_zero (scalar_ne_zero A)) (Filter.Eventually.of_forall ?_)
  intro z
  have h := HolomorphicScalarChartMap.inverse_scalar (scalar_ne_zero A)
    (chart_scalar_relation q A x hx ((toBeltrami q A).symm z))
  simpa only [x, Homeomorph.apply_symm_apply] using h

theorem pullback_regular (x : WholeDeformedAtlas.WholeSurface q A)
    (hx : x ∈ regularSet (WholeDeformedDifferential.form q A)) :
    (WholeDeformedDifferential.form q A).val.toFun x =
      ((scaledForm q A).val.toFun (toBeltrami q A x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (toBeltrami q A) x) := by
  have hreg := (source_regular_iff q A x).mp hx
  have hk := (NativePowerCharts.chosen q x.point).regular_center_exponent_one hreg
  have hs := WholeDeformedDifferential.differential_toFun q A x x (WholeDeformedAtlas.chart_center q A x)
  have ht := NativeBeltramiDifferential.differential_toFun q (parameter A) (toBeltrami q A x) (toBeltrami q A x)
    (NativeBeltramiSurface.chart_center q (parameter A) (toBeltrami q A x))
  simp only [WholeDeformedDifferential.atlasCoefficient, hk, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] at hs
  simp only [NativeBeltramiDifferential.atlasCoefficient, toBeltrami_point, hk, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] at ht
  have hd := HolomorphicScalarChartMap.derivative_relation (toBeltrami q A)
    (WholeDeformedAtlas.chart q A x) (NativeBeltramiSurface.chart q (parameter A) (toBeltrami q A x))
    (forward_mdifferentiable q A x hx)
    (mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (toBeltrami q A x))
      (NativeBeltramiSurface.chart_center q (parameter A) (toBeltrami q A x)))
    (Filter.Eventually.of_forall (chart_scalar_relation q A x hreg))
  change (WholeDeformedDifferential.differential q A).toFun x =
    (scalar A • (NativeBeltramiDifferential.differential q (parameter A)).toFun (toBeltrami q A x)).comp _
  rw [hs, ht]
  exact hd

def equivalence : MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form q A) (scaledForm q A) :=
  MNEC.NativeDifferentialEquivCompletion.of_regular (toBeltrami q A) (regularHomeomorph q A)
    (regularHomeomorph_value q A) (forward_mdifferentiable q A) (inverse_mdifferentiable q A) (pullback_regular q A)

@[simp] theorem equivalence_point (x : WholeDeformedAtlas.WholeSurface q A) :
    ((equivalence q A).homeomorph x).point = x.point := rfl

end VeechDichotomy.SL2BeltramiEquivalence
