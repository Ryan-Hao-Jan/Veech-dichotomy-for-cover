module

public import VeechDichotomy.NativeBeltramiCoverTotalMap

/-! Actual total-family covering coordinates at arbitrary source points.
The powered coordinate identity is derived from the original cover's
native form pullback, including at zeros. One fixed-parameter slice is
analytic by the already constructed genuine native cover. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverCoordinates

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCoverTotalMap
open BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY)

def coordinateMap (y : Y) : ℂ × ℂ → ℂ × ℂ :=
  NativeBeltramiCharts.chart ωX (π.map y) ∘ underlying π ∘ (NativeBeltramiCharts.chart ωY y).symm

def coordinateScalar (y : Y) (p : ℂ × ℂ) : ℂ := (coordinateMap π y p).2

def domain (y : Y) : Set (ℂ × ℂ) := (NativeBeltramiCharts.chart ωY y).target ∩
  (NativeBeltramiCharts.chart ωY y).symm ⁻¹'
    {p : Parameter × Y | π.map p.2 ∈ (NativePowerCharts.chosen ωX (π.map y)).chart.source}

theorem domain_open (y : Y) : IsOpen (domain π y) :=
  (NativeBeltramiCharts.chart ωY y).symm.continuousOn.isOpen_inter_preimage
    (NativeBeltramiCharts.chart ωY y).open_target
    ((NativePowerCharts.chosen ωX (π.map y)).chart.open_source.preimage (π.holomorphic.continuous.comp continuous_snd))

theorem source_center_value (y : Y) (μ : Parameter) :
    NativeBeltramiCharts.chart ωY y (μ, y) = (μ.val, 0) := by
  rw [NativeBeltramiCharts.chart_apply, (NativePowerCharts.chosen ωY y).center_zero, BeltramiPowerLift.rootHomeomorph_zero]

theorem source_inverse_center (y : Y) (μ : Parameter) :
    (NativeBeltramiCharts.chart ωY y).symm (μ.val, 0) = (μ, y) := by
  rw [← source_center_value (ωY := ωY) y μ]
  exact (NativeBeltramiCharts.chart ωY y).left_inv (NativeBeltramiCharts.chart_center ωY y μ)

theorem domain_center (y : Y) (μ : Parameter) : (μ.val, 0) ∈ domain π y := by
  refine ⟨?_, ?_⟩
  · have h := (NativeBeltramiCharts.chart ωY y).map_source (NativeBeltramiCharts.chart_center ωY y μ)
    rwa [source_center_value (ωY := ωY) y μ] at h
  · change π.map ((NativeBeltramiCharts.chart ωY y).symm (μ.val, 0)).2 ∈
      (NativePowerCharts.chosen ωX (π.map y)).chart.source
    rw [source_inverse_center]
    exact (NativePowerCharts.chosen ωX (π.map y)).center

theorem coordinate_first (y : Y) {p : ℂ × ℂ} (hp : p ∈ (NativeBeltramiCharts.chart ωY y).target) :
    (coordinateMap π y p).1 = p.1 := by
  change ((NativeBeltramiCharts.chart ωY y).symm p).1.val = p.1
  exact congrArg Prod.fst ((NativeBeltramiCharts.chart ωY y).right_inv hp)

theorem coordinate_continuousAt (y : Y) {p : ℂ × ℂ} (hp : p ∈ domain π y) :
    ContinuousAt (coordinateScalar π y) p := by
  have ht : underlying π ((NativeBeltramiCharts.chart ωY y).symm p) ∈ (NativeBeltramiCharts.chart ωX (π.map y)).source :=
    (NativeBeltramiCharts.chart_source ωX (π.map y) _).mpr hp.2
  have hi : ContinuousAt (NativeBeltramiCharts.chart ωY y).symm p :=
    (NativeBeltramiCharts.chart ωY y).symm.continuousAt hp.1
  have hu : ContinuousAt (underlying π) ((NativeBeltramiCharts.chart ωY y).symm p) :=
    (continuous_underlying π).continuousAt
  have hc : ContinuousAt (fun r : ℂ × ℂ => underlying π ((NativeBeltramiCharts.chart ωY y).symm r)) p := hu.comp hi
  have hb : ContinuousAt (NativeBeltramiCharts.chart ωX (π.map y)) (underlying π ((NativeBeltramiCharts.chart ωY y).symm p)) :=
    (NativeBeltramiCharts.chart ωX (π.map y)).continuousAt ht
  have hall : ContinuousAt (fun r : ℂ × ℂ => NativeBeltramiCharts.chart ωX (π.map y)
      (underlying π ((NativeBeltramiCharts.chart ωY y).symm r))) p :=
    ContinuousAt.comp (f := fun r : ℂ × ℂ => underlying π ((NativeBeltramiCharts.chart ωY y).symm r))
      (g := NativeBeltramiCharts.chart ωX (π.map y)) hb hc
  exact ContinuousAt.comp (f := fun r : ℂ × ℂ => NativeBeltramiCharts.chart ωX (π.map y)
    (underlying π ((NativeBeltramiCharts.chart ωY y).symm r))) (g := Prod.snd) continuous_snd.continuousAt hall

theorem coordinate_continuous_near (y : Y) (μ : Parameter) :
    ∀ᶠ p in 𝓝 (μ.val, 0), ContinuousAt (coordinateScalar π y) p := by
  filter_upwards [(domain_open π y).mem_nhds (domain_center π y μ)] with p hp
  exact coordinate_continuousAt π y hp

theorem original_power_germ (y : Y) :
    ∀ᶠ z in 𝓝 y, (NativePowerCharts.chosen ωX (π.map y)).chart (π.map z) ^
      (NativePowerCharts.chosen ωX (π.map y)).exponent =
        (NativePowerCharts.chosen ωY y).chart z ^ (NativePowerCharts.chosen ωY y).exponent := by
  let pX := NativePowerCharts.chosen ωX (π.map y)
  let pY := NativePowerCharts.chosen ωY y
  have hd (z : Y) (hz : π.map z ∈ pX.chart.source) :
      HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun w => pX.chart (π.map w) ^ pX.exponent) z (ωY.val.toFun z) := by
    rw [pullback_at π z]
    exact (pX.primitive_derivative (π.map z) hz).comp z (π.holomorphic.mdifferentiableAt (by decide)).hasMFDerivAt
  have h := MNEC.NativeLocalPrimitives.difference_germ ωY
    (fun z => pY.chart z ^ pY.exponent) (fun z => pX.chart (π.map z) ^ pX.exponent)
    pY.chart.source (π.map ⁻¹' pX.chart.source) pY.chart.open_source
    (pX.chart.open_source.preimage π.holomorphic.continuous) pY.primitive_derivative hd y ⟨pY.center, pX.center⟩
  simpa only [pX.center_zero, pY.center_zero, zero_pow pX.exponent_pos.ne', zero_pow pY.exponent_pos.ne',
    sub_self, add_zero] using h

theorem coordinate_power_germ (y : Y) (μ : Parameter) :
    ∀ᶠ p in 𝓝 (μ.val, 0), coordinateScalar π y p ^ (NativePowerCharts.chosen ωX (π.map y)).exponent =
      p.2 ^ (NativePowerCharts.chosen ωY y).exponent := by
  have htarget := (domain_center π y μ).1
  have hc : ContinuousAt (fun p : ℂ × ℂ => ((NativeBeltramiCharts.chart ωY y).symm p).2) (μ.val, 0) :=
    continuous_snd.continuousAt.comp ((NativeBeltramiCharts.chart ωY y).symm.continuousAt htarget)
  have hnear : ∀ᶠ p in 𝓝 (μ.val, 0),
      (NativePowerCharts.chosen ωX (π.map y)).chart (π.map ((NativeBeltramiCharts.chart ωY y).symm p).2) ^
        (NativePowerCharts.chosen ωX (π.map y)).exponent =
      (NativePowerCharts.chosen ωY y).chart ((NativeBeltramiCharts.chart ωY y).symm p).2 ^
        (NativePowerCharts.chosen ωY y).exponent := by
    have hg := original_power_germ π y
    have hvalue := source_inverse_center (ωY := ωY) y μ
    have hg' : ∀ᶠ z in 𝓝 ((NativeBeltramiCharts.chart ωY y).symm (μ.val, 0)).2,
        (NativePowerCharts.chosen ωX (π.map y)).chart (π.map z) ^ (NativePowerCharts.chosen ωX (π.map y)).exponent =
          (NativePowerCharts.chosen ωY y).chart z ^ (NativePowerCharts.chosen ωY y).exponent := by rwa [hvalue]
    exact hc hg'
  filter_upwards [(NativeBeltramiCharts.chart ωY y).open_target.mem_nhds htarget, hnear] with p hp hpow
  change (NativeBeltramiCharts.chart ωX (π.map y) (underlying π ((NativeBeltramiCharts.chart ωY y).symm p))).2 ^ _ = _
  rw [NativeBeltramiCharts.chart_power]
  change BeltramiPlane.map ((NativeBeltramiCharts.chart ωY y).symm p).1.val
    ((NativePowerCharts.chosen ωX (π.map y)).chart (π.map ((NativeBeltramiCharts.chart ωY y).symm p).2) ^
      (NativePowerCharts.chosen ωX (π.map y)).exponent) = p.2 ^ (NativePowerCharts.chosen ωY y).exponent
  rw [hpow, ← NativeBeltramiCharts.chart_power]
  exact congrArg (fun r : ℂ × ℂ => r.2 ^ (NativePowerCharts.chosen ωY y).exponent)
    ((NativeBeltramiCharts.chart ωY y).right_inv hp)

theorem slice_value (y : Y) (μ : Parameter) (z : ℂ) :
    coordinateScalar π y (μ.val, z) = NativeBeltramiSurface.chart ωX μ ⟨π.map y⟩
      ((NativeBeltramiCover.cover π μ).map ((NativeBeltramiSurface.chart ωY μ ⟨y⟩).symm z)) := by
  dsimp only [coordinateScalar, coordinateMap, Function.comp_apply]
  rw [NativeBeltramiSurface.inverse_value ωY μ (⟨y⟩ : NativeBeltramiSurface.Surface ωY μ) z]
  rfl

theorem slice_analytic (y : Y) (μ : Parameter) : AnalyticAt ℂ (fun z => coordinateScalar π y (μ.val, z)) 0 := by
  let s := NativeBeltramiSurface.chart ωY μ (⟨y⟩ : NativeBeltramiSurface.Surface ωY μ)
  let t := NativeBeltramiSurface.chart ωX μ (⟨π.map y⟩ : NativeBeltramiSurface.Surface ωX μ)
  have hs : (0 : ℂ) ∈ s.target := by
    rw [← NativeBeltramiSurface.chart_center_zero ωY μ ⟨y⟩]
    exact s.map_source (NativeBeltramiSurface.chart_center ωY μ ⟨y⟩)
  have hzero : s.symm 0 = ⟨y⟩ := by
    rw [← NativeBeltramiSurface.chart_center_zero ωY μ ⟨y⟩]
    exact s.left_inv (NativeBeltramiSurface.chart_center ωY μ ⟨y⟩)
  have ht : (NativeBeltramiCover.cover π μ).map (s.symm 0) ∈ t.source := by
    rw [hzero]
    exact NativeBeltramiSurface.chart_center ωX μ ⟨π.map y⟩
  have hInv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s.symm 0 :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := (⟨y⟩ : NativeBeltramiSurface.Surface ωY μ))).contMDiffAt (s.open_target.mem_nhds hs)
  have hTarget : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω t ((NativeBeltramiCover.cover π μ).map (s.symm 0)) :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (x := (⟨π.map y⟩ : NativeBeltramiSurface.Surface ωX μ))).contMDiffAt (t.open_source.mem_nhds ht)
  have hh : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (t ∘ (NativeBeltramiCover.cover π μ).map ∘ s.symm) 0 :=
    hTarget.comp 0 (((NativeBeltramiCover.cover π μ).holomorphic _).comp 0 hInv)
  have heq : (fun z => coordinateScalar π y (μ.val, z)) = t ∘ (NativeBeltramiCover.cover π μ).map ∘ s.symm :=
    funext (slice_value π y μ)
  rw [heq]
  exact hh.contDiffAt.analyticAt

end VeechDichotomy.NativeBeltramiCoverCoordinates
