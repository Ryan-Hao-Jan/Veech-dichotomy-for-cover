module

public import VeechDichotomy.NativeUniformMarkTransport

/-! One fixed open neighborhood of the entire old critical set works for
every parameter in the constructed marked-cover family. On this neighborhood
the moved maps are holomorphic in the OLD source structure, with exactly
the old critical points. No parameter-dependent shrinking is needed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformCriticalNeighborhood

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (S : NativeUniformMarkTransport.Transport b)

def region : Set Y := π.map ⁻¹' ⋃ i, S.region i

theorem region_open : IsOpen (region π S) :=
  (isOpen_iUnion S.region_open).preimage π.holomorphic.continuous

theorem critical_subset (hBranch : range b = branchValues π) : criticalSet π ⊆ region π S := by
  intro y hy
  have hb : π.map y ∈ range b := by rw [hBranch]; exact ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := hb
  exact mem_iUnion.mpr ⟨i, hi ▸ S.region_contains i⟩

theorem analytic (u : S.marks.neighborhood) {z : Y} (hz : z ∈ region π S) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (NativeMovingCoverMap.map π (S.marks.transport u)) z ∧
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeMovingCoverMap.map π (S.marks.transport u)) z = 0 ↔
        z ∈ criticalSet π) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  have hf := S.holomorphic u i (π.map z) hi
  have hb := S.inverse_holomorphic u i (π.map z) hi
  exact ⟨hf.comp z (π.holomorphic.mdifferentiableAt (by decide)),
    NativeMovingCoverRegularity.derivative_zero_iff π (S.marks.transport u) z hf hb⟩

def chart (y : Y) : OpenPartialHomeomorph Y ℂ := (chartAt ℂ y).restr (region π S)

theorem chart_center {y : Y} (hy : y ∈ region π S) : y ∈ (chart π S y).source := by
  refine ⟨mem_chart_source ℂ y, ?_⟩
  rw [(region_open π S).interior_eq]
  exact hy

theorem chart_mdifferentiable (y : Y) : (chart π S y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  ComplexAtlasTools.mdifferentiable_restr _ (mdifferentiable_chart y) _

theorem critical_chart_center (hBranch : range b = branchValues π) {y : Y} (hy : y ∈ criticalSet π) :
    y ∈ (chart π S y).source := chart_center π S (critical_subset π S hBranch hy)

end VeechDichotomy.UniformCriticalNeighborhood
