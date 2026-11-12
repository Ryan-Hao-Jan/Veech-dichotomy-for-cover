module

public import VeechDichotomy.RelocatedCoverTransitions

/-! The constructed whole compact source complex curve for moved branch
values, including all critical points. Its topology is literally the
original source topology; only the complex chart structure changes. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverAtlas

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts RelocatedCoverTransitions
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

structure Surface (π : Cover ωX ωY) (ψ : X ≃ₜ X)
    (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
    (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x) where
  point : Y

variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

instance topology : TopologicalSpace (Surface π ψ hψ hInv) :=
  TopologicalSpace.induced Surface.point inferInstance

def toOriginal : Surface π ψ hψ hInv ≃ₜ Y where
  toFun := Surface.point
  invFun := fun y => ⟨y⟩
  left_inv y := by cases y; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (Surface π ψ hψ hInv) :=
  (toOriginal π ψ hψ hInv).isEmbedding.t2Space

instance compactSpace : CompactSpace (Surface π ψ hψ hInv) :=
  (toOriginal π ψ hψ hInv).symm.compactSpace

instance connectedSpace : ConnectedSpace (Surface π ψ hψ hInv) :=
  (toOriginal π ψ hψ hInv).symm.surjective.connectedSpace (toOriginal π ψ hψ hInv).symm.continuous

def chart (i : Surface π ψ hψ hInv) : OpenPartialHomeomorph (Surface π ψ hψ hInv) ℂ :=
  (toOriginal π ψ hψ hInv).transOpenPartialHomeomorph (rawChart π ψ hψ hInv i.point)

theorem chart_center (i : Surface π ψ hψ hInv) : i ∈ (chart π ψ hψ hInv i).source :=
  rawChart_center π ψ hψ hInv i.point

theorem chart_source (i : Surface π ψ hψ hInv) :
    (chart π ψ hψ hInv i).source = Surface.point ⁻¹' (rawChart π ψ hψ hInv i.point).source := rfl

theorem chart_apply (i y : Surface π ψ hψ hInv) :
    chart π ψ hψ hInv i y = rawChart π ψ hψ hInv i.point y.point := rfl

theorem chart_symm_point (i : Surface π ψ hψ hInv) (z : ℂ) :
    ((chart π ψ hψ hInv i).symm z).point = (rawChart π ψ hψ hInv i.point).symm z := rfl

theorem transition_contDiffOn (n : ℕ∞ω) (i j : Surface π ψ hψ hInv) :
    ContDiffOn ℂ n ((chart π ψ hψ hInv i).symm.trans (chart π ψ hψ hInv j))
      ((chart π ψ hψ hInv i).symm.trans (chart π ψ hψ hInv j)).source := by
  change ContDiffOn ℂ n ((rawChart π ψ hψ hInv i.point).symm.trans (rawChart π ψ hψ hInv j.point))
    ((rawChart π ψ hψ hInv i.point).symm.trans (rawChart π ψ hψ hInv j.point)).source
  exact raw_transition_contDiffOn π ψ hψ hInv n i.point j.point

@[instance_reducible] def chartedSpace : ChartedSpace ℂ (Surface π ψ hψ hInv) where
  atlas := range (chart π ψ hψ hInv)
  chartAt := chart π ψ hψ hInv
  mem_chart_source := chart_center π ψ hψ hInv
  chart_mem_atlas i := ⟨i, rfl⟩

theorem isComplexManifold (n : ℕ∞ω) :
    letI := chartedSpace π ψ hψ hInv
    IsManifold 𝓘(ℂ) n (Surface π ψ hψ hInv) := by
  let := chartedSpace π ψ hψ hInv
  let : HasGroupoid (Surface π ψ hψ hInv) (contDiffGroupoid n 𝓘(ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid n 𝓘(ℂ))
    intro e f he hf
    change e ∈ range (chart π ψ hψ hInv) at he
    change f ∈ range (chart π ψ hψ hInv) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_contDiffOn π ψ hψ hInv n i j
  exact IsManifold.mk' 𝓘(ℂ) n (Surface π ψ hψ hInv)

attribute [instance] chartedSpace isComplexManifold

end VeechDichotomy.RelocatedCoverAtlas
