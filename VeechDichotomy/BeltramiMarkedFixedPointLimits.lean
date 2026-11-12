module

public import VeechDichotomy.PositiveMassFiberLimits
public import VeechDichotomy.BeltramiMarkedScaledFamily

/-! Fixed-point accumulation in the ACTUAL native marked family. Its
properness, countability, exact native limit fiber and continuous
inclusion maps discharge the abstract topological obligations. The
positive source-mass bound and conull source set remain explicit here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFixedPointLimits

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory
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

theorem fixed_point {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (p : ℕ → Base A) (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀))
    (f : ∀ n, Z → BeltramiMarkedFiberSurface.Surface π F hBranch (p n).2) (hf : ∀ n, Continuous (f n))
    {C : Set (Total π F hBranch)} (hC : IsClosed C)
    {δ : ℝ≥0∞} (hδpos : 0 < δ)
    (hmass : ∃ᶠ n in atTop, δ ≤ μ ((fun z => inclusion π F hBranch (p n) (f n z)) ⁻¹' C))
    {E : Set Z} (hE : μ Eᶜ = 0) :
    ∃ z ∈ E, ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      inclusion π F hBranch p₀ y ∈ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n)) (f (σ n) z)) atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  let : SecondCountableTopology Y := ChartedSpace.secondCountable_of_sigmaCompact ℂ Y
  let : SecondCountableTopology (BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch) :=
    (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).isEmbedding.secondCountableTopology
  let : MeasurableSpace (Total π F hBranch) := borel _
  let : BorelSpace (Total π F hBranch) := ⟨rfl⟩
  have hmap : ∀ n, Continuous (fun z => inclusion π F hBranch (p n) (f n z)) :=
    fun n => (holomorphic_inclusion π F hBranch (p n)).continuous.comp (hf n)
  obtain ⟨z, hzE, y, hyC, hy, σ, hσ, hlim⟩ := PositiveMassFiberLimits.fixed_point μ
    (projection π F hBranch) (proper_projection π F hBranch)
    (fun n z => inclusion π F hBranch (p n) (f n z)) p p₀ hp
    (fun n z => projection_inclusion π F hBranch (p n) (f n z)) hC
    (fun n => hC.measurableSet.preimage (hmap n).measurable) hδpos hmass hE
  let y₀ := (fiberHomeomorph π F hBranch p₀).symm ⟨y, hy⟩
  have hyy : inclusion π F hBranch p₀ y₀ = y :=
    congrArg Subtype.val ((fiberHomeomorph π F hBranch p₀).apply_symm_apply ⟨y, hy⟩)
  refine ⟨z, hzE, y₀, ?_, σ, hσ, ?_⟩
  · rwa [hyy]
  · rwa [hyy]

end VeechDichotomy.BeltramiMarkedFixedPointLimits
