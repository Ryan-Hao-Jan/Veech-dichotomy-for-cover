module

public import VeechDichotomy.NativePowerCharts
public import VeechDichotomy.SL2PowerLift
public import VeechDichotomy.AnalyticPowerBranch
public import MNEC.NativeLocalPrimitives

/-! Whole-surface complex charts for the SL2 deformation, including all
zeros. Native power charts are chosen at every original point. Their
deformed charts use the proved homeomorphic lift through each power map.
Holomorphic compatibility follows from actual primitive differences;
overlaps containing a zero use the proved zero-isolation property.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.WholeDeformedAtlas

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open LinearGroup SL2PowerLift Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure WholeSurface (q : Differential X) (A : SL2) where
  point : X

instance topology (q : Differential X) (A : SL2) : TopologicalSpace (WholeSurface q A) :=
  TopologicalSpace.induced WholeSurface.point inferInstance

def toOriginal (q : Differential X) (A : SL2) : WholeSurface q A ≃ₜ X where
  toFun := WholeSurface.point
  invFun := fun x => ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

theorem point_injective (q : Differential X) (A : SL2) :
    Function.Injective (WholeSurface.point : WholeSurface q A → X) :=
  (toOriginal q A).injective

instance t2Space (q : Differential X) (A : SL2) : T2Space (WholeSurface q A) :=
  (toOriginal q A).isEmbedding.t2Space

instance compactSpace (q : Differential X) (A : SL2) : CompactSpace (WholeSurface q A) :=
  (toOriginal q A).symm.compactSpace

instance connectedSpace (q : Differential X) (A : SL2) : ConnectedSpace (WholeSurface q A) :=
  (toOriginal q A).symm.surjective.connectedSpace (toOriginal q A).symm.continuous

abbrev powerAt (q : Differential X) (b : X) := NativePowerCharts.chosen q b

def chart (q : Differential X) (A : SL2) (i : WholeSurface q A) :
    OpenPartialHomeomorph (WholeSurface q A) ℂ :=
  (toOriginal q A).transOpenPartialHomeomorph
    ((powerAt q i.point).chart.transHomeomorph
      (SL2PowerLift.rootHomeomorph A (powerAt q i.point).exponent (powerAt q i.point).exponent_pos))

theorem chart_source (q : Differential X) (A : SL2) (i : WholeSurface q A) :
    (chart q A i).source = WholeSurface.point ⁻¹' (powerAt q i.point).chart.source := rfl

theorem chart_apply (q : Differential X) (A : SL2) (i y : WholeSurface q A) :
    chart q A i y = SL2PowerLift.rootHomeomorph A (powerAt q i.point).exponent
      (powerAt q i.point).exponent_pos ((powerAt q i.point).chart y.point) := rfl

theorem chart_center (q : Differential X) (A : SL2) (i : WholeSurface q A) :
    i ∈ (chart q A i).source := (powerAt q i.point).center

theorem chart_center_zero (q : Differential X) (A : SL2) (i : WholeSurface q A) :
    chart q A i i = 0 := by
  rw [chart_apply, (powerAt q i.point).center_zero, SL2PowerLift.rootHomeomorph_zero]

theorem chart_eq_zero_iff (q : Differential X) (A : SL2) (i y : WholeSurface q A)
    (hy : y ∈ (chart q A i).source) : chart q A i y = 0 ↔ y = i := by
  constructor
  · intro h
    exact (chart q A i).injOn hy (chart_center q A i) (h.trans (chart_center_zero q A i).symm)
  · intro h
    subst y
    exact chart_center_zero q A i

theorem chart_power (q : Differential X) (A : SL2) (i y : WholeSurface q A) :
    chart q A i y ^ (powerAt q i.point).exponent =
      complexAction A ((powerAt q i.point).chart y.point ^ (powerAt q i.point).exponent) :=
  SL2PowerLift.rootHomeomorph_pow A _ _ _

theorem action_add (A : SL2) (z w : ℂ) :
    complexAction A (z + w) = complexAction A z + complexAction A w := by
  simp only [complexAction, map_add]

theorem power_difference_germ (q : Differential X) (A : SL2) (i j x : WholeSurface q A)
    (hxi : x ∈ (chart q A i).source) (hxj : x ∈ (chart q A j).source) :
    ∃ c : ℂ, ∀ᶠ y in 𝓝 x,
      chart q A j y ^ (powerAt q j.point).exponent =
        chart q A i y ^ (powerAt q i.point).exponent + c := by
  let pi := powerAt q i.point
  let pj := powerAt q j.point
  have h := MNEC.NativeLocalPrimitives.difference_germ q
    (fun y => pi.chart y ^ pi.exponent) (fun y => pj.chart y ^ pj.exponent)
    pi.chart.source pj.chart.source pi.chart.open_source pj.chart.open_source
    pi.primitive_derivative pj.primitive_derivative x.point ⟨hxi, hxj⟩
  have hnear := (toOriginal q A).continuous.continuousAt h
  refine ⟨complexAction A (pj.chart x.point ^ pj.exponent - pi.chart x.point ^ pi.exponent), ?_⟩
  filter_upwards [hnear] with y hy
  change pj.chart y.point ^ pj.exponent = pi.chart y.point ^ pi.exponent +
    (pj.chart x.point ^ pj.exponent - pi.chart x.point ^ pi.exponent) at hy
  rw [chart_power, chart_power]
  change complexAction A (pj.chart y.point ^ pj.exponent) =
    complexAction A (pi.chart y.point ^ pi.exponent) +
      complexAction A (pj.chart x.point ^ pj.exponent - pi.chart x.point ^ pi.exponent)
  rw [hy, action_add]

theorem transition_power_germ (q : Differential X) (A : SL2) (i j : WholeSurface q A)
    (z : ℂ) (hz : z ∈ ((chart q A i).symm.trans (chart q A j)).source) :
    ∃ c : ℂ, ∀ᶠ w in 𝓝 z,
      (((chart q A i).symm.trans (chart q A j)) w) ^ (powerAt q j.point).exponent =
        w ^ (powerAt q i.point).exponent + c := by
  let x := (chart q A i).symm z
  have hxi : x ∈ (chart q A i).source := (chart q A i).map_target hz.1
  have hxj : x ∈ (chart q A j).source := hz.2
  obtain ⟨c, hc⟩ := power_difference_germ q A i j x hxi hxj
  have hcont := (chart q A i).symm.continuousAt hz.1
  refine ⟨c, ?_⟩
  filter_upwards [(chart q A i).open_target.mem_nhds hz.1, hcont hc] with w hw hdiff
  change chart q A j ((chart q A i).symm w) ^ (powerAt q j.point).exponent = _
  change chart q A j ((chart q A i).symm w) ^ (powerAt q j.point).exponent =
    chart q A i ((chart q A i).symm w) ^ (powerAt q i.point).exponent + c at hdiff
  rw [(chart q A i).right_inv hw] at hdiff
  exact hdiff

theorem zero_in_chart_eq_center (q : Differential X) (A : SL2) (i x : WholeSurface q A)
    (hxi : x ∈ (chart q A i).source) (hxzero : x.point ∈ zeroSet q) : x = i :=
  point_injective q A ((powerAt q i.point).zero_in_source_eq_center hxi hxzero)

theorem power_derivative_ne_zero_at_regular (q : Differential X) (A : SL2)
    (j x : WholeSurface q A) (hxj : x ∈ (chart q A j).source)
    (hxreg : x.point ∈ regularSet q) :
    ((powerAt q j.point).exponent : ℂ) *
      chart q A j x ^ ((powerAt q j.point).exponent - 1) ≠ 0 := by
  by_cases hzero : chart q A j x = 0
  · have hxjEq := (chart_eq_zero_iff q A j x hxj).mp hzero
    have hjreg : j.point ∈ regularSet q := by rw [← hxjEq]; exact hxreg
    have hk := (powerAt q j.point).regular_center_exponent_one hjreg
    simp only [hk, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, ne_eq, one_ne_zero, not_false_eq_true]
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr (powerAt q j.point).exponent_pos.ne')
      (pow_ne_zero _ hzero)

theorem transition_analyticAt (q : Differential X) (A : SL2) (i j : WholeSurface q A)
    (z : ℂ) (hz : z ∈ ((chart q A i).symm.trans (chart q A j)).source) :
    AnalyticAt ℂ ((chart q A i).symm.trans (chart q A j)) z := by
  classical
  let x := (chart q A i).symm z
  have hxi : x ∈ (chart q A i).source := (chart q A i).map_target hz.1
  have hxj : x ∈ (chart q A j).source := hz.2
  by_cases hzero : x.point ∈ zeroSet q
  · have hix : x = i := zero_in_chart_eq_center q A i x hxi hzero
    have hjx : x = j := zero_in_chart_eq_center q A j x hxj hzero
    have hij : i = j := hix.symm.trans hjx
    rw [← hij]
    have heq : (id : ℂ → ℂ) =ᶠ[𝓝 z] ((chart q A i).symm.trans (chart q A i)) := by
      filter_upwards [(chart q A i).open_target.mem_nhds hz.1] with w hw
      exact ((chart q A i).right_inv hw).symm
    exact analyticAt_id.congr heq
  · have hxreg : x.point ∈ regularSet q := hzero
    obtain ⟨c, hc⟩ := transition_power_germ q A i j z hz
    have heq : (fun w => (((chart q A i).symm.trans (chart q A j)) w) ^
        (powerAt q j.point).exponent) =ᶠ[𝓝 z] fun w => w ^ (powerAt q i.point).exponent + c := hc
    have hp : AnalyticAt ℂ (fun w => (((chart q A i).symm.trans (chart q A j)) w) ^
        (powerAt q j.point).exponent) z :=
      ((analyticAt_id.pow (powerAt q i.point).exponent).add analyticAt_const).congr heq.symm
    have hcont := ((chart q A i).symm.trans (chart q A j)).continuousAt hz
    exact AnalyticPowerBranch.analyticAt_of_power hcont hp
      (power_derivative_ne_zero_at_regular q A j x hxj hxreg)

@[instance_reducible] def chartedSpace (q : Differential X) (A : SL2) :
    ChartedSpace ℂ (WholeSurface q A) where
  atlas := range (chart q A)
  chartAt := chart q A
  mem_chart_source := chart_center q A
  chart_mem_atlas i := ⟨i, rfl⟩

theorem isComplexManifold (q : Differential X) (A : SL2) (n : ℕ∞ω) :
    letI := chartedSpace q A
    IsManifold 𝓘(ℂ) n (WholeSurface q A) := by
  let := chartedSpace q A
  let : HasGroupoid (WholeSurface q A) (contDiffGroupoid n 𝓘(ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid n 𝓘(ℂ))
    intro e f he hf
    change e ∈ range (chart q A) at he
    change f ∈ range (chart q A) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    have hdiff : ContDiffOn ℂ n ((chart q A i).symm.trans (chart q A j))
        ((chart q A i).symm.trans (chart q A j)).source :=
      fun z hz => (transition_analyticAt q A i j z hz).contDiffAt.contDiffWithinAt
    simpa only [contDiffPregroupoid, mfld_simps] using hdiff
  exact IsManifold.mk' 𝓘(ℂ) n (WholeSurface q A)

end VeechDichotomy.WholeDeformedAtlas
