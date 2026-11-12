module

public import VeechDichotomy.SL2BeltramiParameters
public import VeechDichotomy.NativeBeltramiDifferential
public import VeechDichotomy.WholeDeformedDifferential

/-! Literal whole-surface and regular-locus comparisons between the native
SL2 deformation and its scalar-rescaled unit-disk fiber. At regular centers
the actual power charts have exponent one, yielding a scalar chart identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2BeltramiComparisonCharts

open MNEC.NativeAbelianDifferential LinearGroup SL2BeltramiParameters Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

def scaledForm : Differential (NativeBeltramiSurface.Surface q (parameter A)) :=
  ⟨scalar A • (NativeBeltramiDifferential.form q (parameter A)).val,
    smul_ne_zero (scalar_ne_zero A) (NativeBeltramiDifferential.differential_ne_zero q (parameter A))⟩

theorem scaled_zero_iff (y : NativeBeltramiSurface.Surface q (parameter A)) :
    (scaledForm q A).val.toFun y = 0 ↔ y.point ∈ zeroSet q := by
  have hzero : scalar A • (NativeBeltramiDifferential.form q (parameter A)).val.toFun y = 0 ↔
      (NativeBeltramiDifferential.form q (parameter A)).val.toFun y = 0 :=
    ⟨fun h => (smul_eq_zero.mp h).resolve_left (scalar_ne_zero A), fun h => smul_eq_zero.mpr (Or.inr h)⟩
  exact hzero.trans (NativeBeltramiDifferential.pointwise_zero_iff q (parameter A) y)

theorem source_regular_iff (x : WholeDeformedAtlas.WholeSurface q A) :
    x ∈ regularSet (WholeDeformedDifferential.form q A) ↔ x.point ∈ regularSet q :=
  not_congr (WholeDeformedDifferential.pointwise_zero_iff q A x)

theorem target_regular_iff (y : NativeBeltramiSurface.Surface q (parameter A)) :
    y ∈ regularSet (scaledForm q A) ↔ y.point ∈ regularSet q := not_congr (scaled_zero_iff q A y)

def toBeltrami : WholeDeformedAtlas.WholeSurface q A ≃ₜ NativeBeltramiSurface.Surface q (parameter A) :=
  (WholeDeformedAtlas.toOriginal q A).trans (NativeBeltramiSurface.toOriginal q (parameter A)).symm

@[simp] theorem toBeltrami_point (x : WholeDeformedAtlas.WholeSurface q A) : (toBeltrami q A x).point = x.point := rfl
@[simp] theorem toBeltrami_symm_point (y : NativeBeltramiSurface.Surface q (parameter A)) :
    ((toBeltrami q A).symm y).point = y.point := rfl

def regularHomeomorph : regularSet (WholeDeformedDifferential.form q A) ≃ₜ regularSet (scaledForm q A) :=
  (toBeltrami q A).subtype (p := fun x => x ∈ regularSet (WholeDeformedDifferential.form q A))
    (q := fun y => y ∈ regularSet (scaledForm q A)) (by
      intro x
      exact (source_regular_iff q A x).trans (target_regular_iff q A (toBeltrami q A x)).symm)

theorem regularHomeomorph_value (x : regularSet (WholeDeformedDifferential.form q A)) :
    (regularHomeomorph q A x).val = toBeltrami q A x.val := rfl

theorem chart_sources (i z : WholeDeformedAtlas.WholeSurface q A) :
    toBeltrami q A z ∈ (NativeBeltramiSurface.chart q (parameter A) (toBeltrami q A i)).source ↔
      z ∈ (WholeDeformedAtlas.chart q A i).source := Iff.rfl

theorem chart_scalar_relation (i : WholeDeformedAtlas.WholeSurface q A) (hi : i.point ∈ regularSet q)
    (z : WholeDeformedAtlas.WholeSurface q A) :
    WholeDeformedAtlas.chart q A i z = scalar A * NativeBeltramiSurface.chart q (parameter A)
      (toBeltrami q A i) (toBeltrami q A z) := by
  have hk := (NativePowerCharts.chosen q i.point).regular_center_exponent_one hi
  have hs := WholeDeformedAtlas.chart_power q A i z
  have ht := NativeBeltramiCharts.chart_power q i.point (parameter A, z.point)
  simp only [hk, pow_one] at hs ht
  change NativeBeltramiSurface.chart q (parameter A) (toBeltrami q A i) (toBeltrami q A z) =
    BeltramiPlane.map (parameter A).val ((NativePowerCharts.chosen q i.point).chart z.point) at ht
  calc
    WholeDeformedAtlas.chart q A i z = SL2PowerLift.complexAction A ((NativePowerCharts.chosen q i.point).chart z.point) := hs
    _ = scalar A * BeltramiPlane.map (parameter A).val ((NativePowerCharts.chosen q i.point).chart z.point) := factorization A _
    _ = _ := congrArg (fun w : ℂ => scalar A * w) ht.symm

end VeechDichotomy.SL2BeltramiComparisonCharts
