module

public import VeechDichotomy.FiniteSimultaneousLimits
public import VeechDichotomy.BeltramiMarkedSL2SourceMaps

/-! For finitely many prescribed regular-limit neighborhoods, genuine
SL2 source comparison maps admit fixed points in any conull set with
limits in all those neighborhoods along ONE common subsequence. This
supplies the simultaneous-time requirement of a rectangle-chain proof. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedSimultaneousLimits

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

variable {X Y Z I : Type*} [Finite I]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (D : ℕ → SL2) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (transformed q (D n)) (fiberForm π F hBranch (p n)))

theorem common_subsequence (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀))
    (hzero : ∀ k, p₀.2.val.2 k = 0) {E : Set Z} (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (x₀ : I → BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : ∀ i, x₀ i ∈ regularSet (fiberForm π F hBranch p₀))
    (W : I → Set (Total π F hBranch)) (hW : ∀ i, IsOpen (W i))
    (hxW : ∀ i, inclusion π F hBranch p₀ (x₀ i) ∈ W i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i, ∃ z ∈ E,
      ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
        y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y ∈ W i ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedSL2SourceMaps.homeomorph π F hBranch q D p e (σ n) z)) atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  let f := fun n z => inclusion π F hBranch (p n) (BeltramiMarkedSL2SourceMaps.homeomorph π F hBranch q D p e n z)
  let R := fun i z t => z ∈ E ∧ ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
    y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y = t ∧ t ∈ W i
  have hselect : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∃ (z : Z) (y : Total π F hBranch) (ψ : ℕ → ℕ), StrictMono ψ ∧ R i z y ∧
        Tendsto (fun n => f (φ (ψ n)) z) atTop (𝓝 y) := by
    intro φ hφ i
    obtain ⟨z, hzE, y, hyreg, hyW, ψ, hψ, hlim⟩ := BeltramiMarkedSL2SourceMaps.conull_limit_density π F hBranch
      q (D ∘ φ) (p ∘ φ) (fun n => e (φ n)) p₀ (hp.comp hφ.tendsto_atTop) hzero hE (x₀ i) (hx₀ i) (hW i) (hxW i)
    exact ⟨z, inclusion π F hBranch p₀ y, ψ, hψ, ⟨hzE, y, hyreg, rfl, hyW⟩, hlim⟩
  obtain ⟨σ, hσ, hsim⟩ := FiniteSimultaneousLimits.simultaneous f R hselect
  refine ⟨σ, hσ, ?_⟩
  intro i
  obtain ⟨z, t, ⟨hzE, y, hyreg, hyt, hyW⟩, hlim⟩ := hsim i
  refine ⟨z, hzE, y, hyreg, ?_, ?_⟩
  · rwa [hyt]
  · rwa [hyt]

end VeechDichotomy.BeltramiMarkedSimultaneousLimits
