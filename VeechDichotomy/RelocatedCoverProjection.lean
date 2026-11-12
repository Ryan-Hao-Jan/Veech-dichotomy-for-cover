module

public import VeechDichotomy.RelocatedCoverAtlas
public import VeechDichotomy.HolomorphicCurveMaps

/-! The actual moved map is holomorphic for the constructed whole-source
complex structure. At regular points its nonzero derivative is proved
from the literal pulled-chart equation, not assumed as cover data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverProjection

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open RelocatedCoverTransitions RelocatedCoverAtlas Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

def map (y : Surface π ψ hψ hInv) : X := projection π ψ y.point

theorem continuous_map : Continuous (map π ψ hψ hInv) :=
  (NativeMovingCoverMap.continuous_map π ψ).comp (toOriginal π ψ hψ hInv).continuous

theorem surjective_map : Function.Surjective (map π ψ hψ hInv) :=
  (NativeMovingCoverMap.surjective_map π ψ).comp (toOriginal π ψ hψ hInv).surjective

theorem finite_fibers (x : X) : (map π ψ hψ hInv ⁻¹' {x}).Finite := by
  apply ((NativeMovingCoverMap.finite_fibers π ψ x).image (toOriginal π ψ hψ hInv).symm).subset
  intro y hy
  exact ⟨y.point, hy, (toOriginal π ψ hψ hInv).symm_apply_apply y⟩

local instance : ChartedSpace ℂ (Surface π ψ hψ hInv) := RelocatedCoverAtlas.chartedSpace π ψ hψ hInv
local instance : IsManifold 𝓘(ℂ) ω (Surface π ψ hψ hInv) := RelocatedCoverAtlas.isComplexManifold π ψ hψ hInv ω

theorem chart_regular_apply {i : Surface π ψ hψ hInv} (hi : i.point ∉ criticalSet π) (z : Surface π ψ hψ hInv) :
    chart π ψ hψ hInv i z = baseChart π ψ ⟨i.point, hi⟩ (map π ψ hψ hInv z) := by
  rw [chart_apply, rawChart_regular π ψ hψ hInv hi]
  exact regularChart_apply π ψ ⟨i.point, hi⟩ z.point

theorem regular_factor {i : Surface π ψ hψ hInv} (hi : i.point ∉ criticalSet π) {z : Surface π ψ hψ hInv}
    (hz : z ∈ (chart π ψ hψ hInv i).source) :
    map π ψ hψ hInv z = (baseChart π ψ ⟨i.point, hi⟩).symm (chart π ψ hψ hInv i z) := by
  have hzold : z.point ∈ (rawChart π ψ hψ hInv i.point).source := hz
  rw [rawChart_regular π ψ hψ hInv hi] at hzold
  have ht : map π ψ hψ hInv z ∈ (baseChart π ψ ⟨i.point, hi⟩).source := by
    have h := hzold.2
    change localMap π ψ ⟨i.point, hi⟩ z.point ∈ (baseChart π ψ ⟨i.point, hi⟩).source at h
    rwa [localMap_apply] at h
  rw [chart_regular_apply π ψ hψ hInv hi]
  exact ((baseChart π ψ ⟨i.point, hi⟩).left_inv ht).symm

theorem mdifferentiableAt_regular {i : Surface π ψ hψ hInv} (hi : i.point ∉ criticalSet π) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π ψ hψ hInv) i := by
  have hC : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i) i :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i) (mem_chart_source ℂ i)
  have hTC : chart π ψ hψ hInv i i ∈ (baseChart π ψ ⟨i.point, hi⟩).target := by
    rw [chart_regular_apply π ψ hψ hInv hi]
    exact (baseChart π ψ ⟨i.point, hi⟩).map_source (mem_chart_source ℂ (map π ψ hψ hInv i))
  have hTInv := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ))
    (chart_mem_atlas ℂ (map π ψ hψ hInv i)) hTC
  apply (hTInv.comp i hC).congr_of_eventuallyEq
  filter_upwards [(chart π ψ hψ hInv i).open_source.mem_nhds (chart_center π ψ hψ hInv i)] with z hz
  exact regular_factor π ψ hψ hInv hi hz

theorem mdifferentiableAt_critical {i : Surface π ψ hψ hInv} (hi : i.point ∈ criticalSet π) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (map π ψ hψ hInv) i := by
  let c := chartAt ℂ i.point
  have hvalue (z : Surface π ψ hψ hInv) : chart π ψ hψ hInv i z = c z.point := by
    rw [chart_apply, rawChart_critical π ψ hψ hInv hi]
    rfl
  have hC : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i) i :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i) (mem_chart_source ℂ i)
  have hOldInv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (chart π ψ hψ hInv i i) := by
    rw [hvalue]
    exact mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i.point)
      (c.map_source (mem_chart_source ℂ i.point))
  have hcenter : c.symm (chart π ψ hψ hInv i i) = i.point := by
    rw [hvalue]
    exact c.left_inv (mem_chart_source ℂ i.point)
  have hOldP : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) (c.symm (chart π ψ hψ hInv i i)) := by
    rw [hcenter]
    exact (criticalNeighborhood_analytic π ψ hψ hInv ⟨i.point, hi⟩
      (criticalNeighborhood_center π ψ hψ hInv ⟨i.point, hi⟩)).1
  apply (hOldP.comp i (hOldInv.comp i hC)).congr_of_eventuallyEq
  filter_upwards [(chart π ψ hψ hInv i).open_source.mem_nhds (chart_center π ψ hψ hInv i)] with z hz
  have hzold : z.point ∈ (rawChart π ψ hψ hInv i.point).source := hz
  rw [rawChart_critical π ψ hψ hInv hi] at hzold
  change projection π ψ z.point = projection π ψ (c.symm (chart π ψ hψ hInv i z))
  rw [hvalue, c.left_inv hzold.1]

theorem mdifferentiable_map : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (map π ψ hψ hInv) := by
  intro i
  by_cases hi : i.point ∈ criticalSet π
  · exact mdifferentiableAt_critical π ψ hψ hInv hi
  · exact mdifferentiableAt_regular π ψ hψ hInv hi

theorem holomorphic_map : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (map π ψ hψ hInv) :=
  HolomorphicCurveMaps.contMDiff_of_mdifferentiable (map π ψ hψ hInv) (mdifferentiable_map π ψ hψ hInv)

theorem derivative_ne_zero_regular {i : Surface π ψ hψ hInv} (hi : i.point ∉ criticalSet π) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ hψ hInv) i ≠ 0 := by
  intro hzero
  have hT := mdifferentiableAt_atlas (I := 𝓘(ℂ))
    (chart_mem_atlas ℂ (map π ψ hψ hInv i)) (mem_chart_source ℂ (map π ψ hψ hInv i))
  have hcomp := hT.hasMFDerivAt.comp i (mdifferentiable_map π ψ hψ hInv i).hasMFDerivAt
  have hC : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i) i
      ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (baseChart π ψ ⟨i.point, hi⟩) (map π ψ hψ hInv i)).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π ψ hψ hInv) i)) :=
    hcomp.congr_of_eventuallyEq_abuse (Filter.Eventually.of_forall (chart_regular_apply π ψ hψ hInv hi))
  have hCzero := hC.mfderiv
  rw [hzero, ContinuousLinearMap.comp_zero] at hCzero
  have hChart := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ i)
  have hinj := (hChart.mfderiv (mem_chart_source ℂ i)).injective
  change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chart π ψ hψ hInv i) i) at hinj
  rw [hCzero] at hinj
  let : Nontrivial (TangentSpace 𝓘(ℂ) i) := inferInstanceAs (Nontrivial ℂ)
  exact Function.not_injective_const hinj

end VeechDichotomy.RelocatedCoverProjection
