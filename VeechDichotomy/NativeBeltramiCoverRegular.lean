module

public import VeechDichotomy.NativeBeltramiDifferential
public import VeechDichotomy.NativeTranslationCover
public import VeechDichotomy.HolomorphicScalarChartMap

/-! The literal underlying finite cover remains holomorphic and preserves
the actual deformed forms on every regular point after simultaneous
unit-disk deformation. The chart translation formula is derived from
the original native cover's genuine pullback identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverRegular

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

section ChartTools
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem powerChart_primitive (q : Differential X) (b : X) (hb : b ∈ regularSet q)
    (x : X) (hx : x ∈ (NativePowerCharts.chosen q b).chart.source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (NativePowerCharts.chosen q b).chart x (q.val.toFun x) := by
  have h := (NativePowerCharts.chosen q b).primitive_derivative x hx
  have heq : (fun z : X => (NativePowerCharts.chosen q b).chart z ^ (NativePowerCharts.chosen q b).exponent) =
      (NativePowerCharts.chosen q b).chart := by
    funext z
    rw [(NativePowerCharts.chosen q b).regular_center_exponent_one hb, pow_one]
  rw [heq] at h
  exact h

theorem regular_iff (q : Differential X) (μ : Parameter) (y : NativeBeltramiSurface.Surface q μ) :
    y ∈ regularSet (NativeBeltramiDifferential.form q μ) ↔ y.point ∈ regularSet q :=
  not_congr (NativeBeltramiDifferential.pointwise_zero_iff q μ y)

theorem chart_regular_value (q : Differential X) (μ : Parameter)
    (i : NativeBeltramiSurface.Surface q μ) (hi : i.point ∈ regularSet q) (y : NativeBeltramiSurface.Surface q μ) :
    NativeBeltramiSurface.chart q μ i y = BeltramiPlane.map μ.val ((NativePowerCharts.chosen q i.point).chart y.point) := by
  have h := NativeBeltramiCharts.chart_power q i.point (μ, y.point)
  simp only [(NativePowerCharts.chosen q i.point).regular_center_exponent_one hi, pow_one] at h
  exact h

end ChartTools

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (μ : Parameter)

def map (y : NativeBeltramiSurface.Surface ωY μ) : NativeBeltramiSurface.Surface ωX μ := ⟨π.map y.point⟩

@[simp] theorem map_point (y : NativeBeltramiSurface.Surface ωY μ) : (map π μ y).point = π.map y.point := rfl

theorem continuous_map : Continuous (map π μ) :=
  (NativeBeltramiSurface.toOriginal ωX μ).symm.continuous.comp
    (π.holomorphic.continuous.comp (NativeBeltramiSurface.toOriginal ωY μ).continuous)

theorem original_chart_germ (y : Y) (hy : y ∈ regularSet ωY) :
    ∀ᶠ z in 𝓝 y, (NativePowerCharts.chosen ωX (π.map y)).chart (π.map z) = (NativePowerCharts.chosen ωY y).chart z := by
  have hbase := regular_maps_to_regular π hy
  have h := local_translation_in_primitive_charts π (NativePowerCharts.chosen ωX (π.map y)).chart
    (NativePowerCharts.chosen ωY y).chart (powerChart_primitive ωX (π.map y) hbase) (powerChart_primitive ωY y hy)
    y (NativePowerCharts.chosen ωY y).center (NativePowerCharts.chosen ωX (π.map y)).center
  simpa only [(NativePowerCharts.chosen ωX (π.map y)).center_zero, (NativePowerCharts.chosen ωY y).center_zero,
    sub_self, add_zero] using h

theorem chart_germ (y : NativeBeltramiSurface.Surface ωY μ) (hy : y.point ∈ regularSet ωY) :
    ∀ᶠ z in 𝓝 y, NativeBeltramiSurface.chart ωX μ (map π μ y) (map π μ z) = NativeBeltramiSurface.chart ωY μ y z := by
  have h := (NativeBeltramiSurface.toOriginal ωY μ).continuous.continuousAt (original_chart_germ π y.point hy)
  filter_upwards [h] with z hz
  rw [chart_regular_value ωX μ (map π μ y) (regular_maps_to_regular π hy), chart_regular_value ωY μ y hy]
  exact congrArg (BeltramiPlane.map μ.val) hz

theorem regular_mdifferentiable (y : NativeBeltramiSurface.Surface ωY μ)
    (hy : y ∈ regularSet (NativeBeltramiDifferential.form ωY μ)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π μ) y :=
  HolomorphicScalarChartMap.mdifferentiableAt (map π μ) (continuous_map π μ)
    (NativeBeltramiSurface.chart ωY μ y) (NativeBeltramiSurface.chart ωX μ (map π μ y))
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ y))
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (map π μ y)))
    (NativeBeltramiSurface.chart_center ωY μ y) (NativeBeltramiSurface.chart_center ωX μ (map π μ y)) one_ne_zero
    ((chart_germ π μ y ((regular_iff ωY μ y).mp hy)).mono fun _ h => by simpa only [one_mul] using h.symm)

theorem regular_pullback (y : NativeBeltramiSurface.Surface ωY μ)
    (hy : y ∈ regularSet (NativeBeltramiDifferential.form ωY μ)) :
    (NativeBeltramiDifferential.form ωY μ).val.toFun y =
      ((NativeBeltramiDifferential.form ωX μ).val.toFun (map π μ y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π μ) y) := by
  have hreg := (regular_iff ωY μ y).mp hy
  have hkY := (NativePowerCharts.chosen ωY y.point).regular_center_exponent_one hreg
  have hkX := (NativePowerCharts.chosen ωX (π.map y.point)).regular_center_exponent_one (regular_maps_to_regular π hreg)
  have hs := NativeBeltramiDifferential.differential_toFun ωY μ y y (NativeBeltramiSurface.chart_center ωY μ y)
  have ht := NativeBeltramiDifferential.differential_toFun ωX μ (map π μ y) (map π μ y)
    (NativeBeltramiSurface.chart_center ωX μ (map π μ y))
  simp only [NativeBeltramiDifferential.atlasCoefficient, hkY, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] at hs
  simp only [NativeBeltramiDifferential.atlasCoefficient, map_point, hkX, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] at ht
  have hd := HolomorphicScalarChartMap.derivative_relation (c := (1 : ℂ)) (map π μ)
    (NativeBeltramiSurface.chart ωY μ y) (NativeBeltramiSurface.chart ωX μ (map π μ y))
    (regular_mdifferentiable π μ y hy)
    (mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (map π μ y)) (NativeBeltramiSurface.chart_center ωX μ (map π μ y)))
    ((chart_germ π μ y hreg).mono fun _ h => by simpa only [one_mul] using h.symm)
  change (NativeBeltramiDifferential.differential ωY μ).toFun y =
    ((NativeBeltramiDifferential.differential ωX μ).toFun (map π μ y)).comp _
  rw [hs, ht]
  simpa only [one_smul] using! hd

end VeechDichotomy.NativeBeltramiCoverRegular
