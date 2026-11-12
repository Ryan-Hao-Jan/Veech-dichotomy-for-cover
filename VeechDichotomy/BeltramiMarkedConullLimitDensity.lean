module

public import VeechDichotomy.BeltramiMarkedFixedPointLimits
public import VeechDichotomy.BeltramiMarkedPositiveFlatRegions
public import VeechDichotomy.BeltramiMarkedSliceCoordinates
public import MNEC.NativePhysicalArea

/-! Images of fixed points from ANY conull source set accumulate in
every neighborhood of every regular zero-displacement limit point.
Actual persistent flat regions give the positive mass; actual properness
and native fiber identifications give the limit. Source maps preserve
the genuine native physical area; no generic-point or ergodic theorem
is assumed in this geometric/measure step. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedConullLimitDensity

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

local instance (p : Base A) : MeasurableSpace (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) := borel _
local instance (p : Base A) : BorelSpace (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) := ⟨rfl⟩

theorem density {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (p : ℕ → Base A) (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀))
    (hzero : ∀ i, p₀.2.val.2 i = 0)
    (f : ∀ n, Z → BeltramiMarkedFiberSurface.Surface π F hBranch (p n).2) (hf : ∀ n, Continuous (f n))
    (hpres : ∀ n, MeasurePreserving (f n) μ (MNEC.NativePhysicalArea.surfaceArea (fiberForm π F hBranch (p n))))
    {E : Set Z} (hE : μ Eᶜ = 0)
    (x₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) (hx₀ : x₀ ∈ regularSet (fiberForm π F hBranch p₀))
    {W : Set (Total π F hBranch)} (hW : IsOpen W) (hxW : inclusion π F hBranch p₀ x₀ ∈ W) :
    ∃ z ∈ E, ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      inclusion π F hBranch p₀ y ∈ W ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n)) (f (σ n) z)) atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  let : LocallyCompactSpace NonzeroComplexParameter.Parameter := ChartedSpace.locallyCompactSpace
    (H := ℂ) (M := NonzeroComplexParameter.Parameter)
  let : LocallyCompactSpace (BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch) := ChartedSpace.locallyCompactSpace
    (H := ComplexBeltramiMarkParameters.Space (m := m) × ℂ) (M := BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch)
  obtain ⟨C, hC, hxC, hCW⟩ := exists_compact_subset hW hxW
  obtain ⟨U, hU, hpU, v₀, r, _, hvol, hregions⟩ :=
    BeltramiMarkedPositiveFlatRegions.regions π F hBranch p₀ hzero x₀ hx₀ isOpen_interior hxC
  have hmass : ∃ᶠ n in atTop, volume (Metric.ball v₀ r) ≤
      μ ((fun z => inclusion π F hBranch (p n) (f n z)) ⁻¹' C) := by
    apply Filter.Eventually.frequently
    filter_upwards [hp (hU.mem_nhds hpU)] with n hn
    obtain ⟨i, _, harea, hstay⟩ := hregions (p n) hn
    let D := inclusion π F hBranch (p n) ⁻¹' C
    have hD : MeasurableSet D := (hC.isClosed.preimage (holomorphic_inclusion π F hBranch (p n)).continuous).measurableSet
    have hbound : volume (Metric.ball v₀ r) ≤ MNEC.NativePhysicalArea.surfaceArea (fiberForm π F hBranch (p n)) D := by
      rw [MNEC.NativePhysicalArea.surfaceArea_apply _ D hD, ← harea]
      apply measure_mono
      rintro y ⟨v, hv, rfl⟩
      exact (show interior C ⊆ C from interior_subset) (hstay v hv)
    have hEq : μ ((fun z => inclusion π F hBranch (p n) (f n z)) ⁻¹' C) =
        MNEC.NativePhysicalArea.surfaceArea (fiberForm π F hBranch (p n)) D :=
      (hpres n).measure_preimage hD.nullMeasurableSet
    exact hEq.symm ▸ hbound
  obtain ⟨z, hzE, y, hyC, σ, hσ, hlim⟩ := BeltramiMarkedFixedPointLimits.fixed_point π F hBranch μ
    p p₀ hp f hf hC.isClosed hvol hmass hE
  exact ⟨z, hzE, y, hCW hyC, σ, hσ, hlim⟩

theorem density_regular {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (p : ℕ → Base A) (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀))
    (hzero : ∀ i, p₀.2.val.2 i = 0)
    (f : ∀ n, Z → BeltramiMarkedFiberSurface.Surface π F hBranch (p n).2) (hf : ∀ n, Continuous (f n))
    (hpres : ∀ n, MeasurePreserving (f n) μ (MNEC.NativePhysicalArea.surfaceArea (fiberForm π F hBranch (p n))))
    {E : Set Z} (hE : μ Eᶜ = 0)
    (x₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) (hx₀ : x₀ ∈ regularSet (fiberForm π F hBranch p₀))
    {W : Set (Total π F hBranch)} (hW : IsOpen W) (hxW : inclusion π F hBranch p₀ x₀ ∈ W) :
    ∃ z ∈ E, ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y ∈ W ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun n => inclusion π F hBranch (p (σ n)) (f (σ n) z)) atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  let s := (p₀.2, x₀.point)
  have hxS : inclusion π F hBranch p₀ x₀ ∈ BeltramiMarkedSliceCoordinates.source π F hBranch s :=
    BeltramiMarkedLimitFlatCharts.center π F hBranch p₀ x₀
  obtain ⟨z, hzE, y, hyW, σ, hσ, hlim⟩ := density π F hBranch μ p p₀ hp hzero f hf hpres hE x₀ hx₀
    (hW.inter (BeltramiMarkedSliceCoordinates.source_open π F hBranch s)) ⟨hxW, hxS⟩
  have hyS : y ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source := hyW.2
  have hyOld := BeltramiMarkedLimitFlatCharts.original_regular π F hBranch p₀ hzero hx₀
  have hs : s.2 ∉ criticalSet π := fun hc => hyOld (critical_subset_zeroSet π hc)
  have hreg := BeltramiMarkedLimitFlatCharts.base_regular π F p₀.2 hzero hyOld
  exact ⟨z, hzE, y, BeltramiMarkedScaledSlices.regular_source π F hBranch s hs hreg p₀ hyS, hyW.1, σ, hσ, hlim⟩

end VeechDichotomy.BeltramiMarkedConullLimitDensity
