module

public import VeechDichotomy.BeltramiMarkedConullLimitDensity
public import VeechDichotomy.NativeDeformationArea
public import MNEC.NativeDifferentialEquivArea

/-! The actual SL2 deformation followed by an actual native
differential equivalence gives the comparison maps into the constructed
family. Their genuine area preservation discharges the source-measure
input of the fixed-conull-point limit-density theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedSL2SourceMaps

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (D : ℕ → SL2) (p : ℕ → Base A)

local instance (n : ℕ) : ChartedSpace ℂ (WholeSurface q (D n)) := WholeDeformedAtlas.chartedSpace q (D n)
local instance (n : ℕ) : IsManifold 𝓘(ℂ) ω (WholeSurface q (D n)) := WholeDeformedAtlas.isComplexManifold q (D n) ω
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩
local instance (a : Base A) : MeasurableSpace (BeltramiMarkedFiberSurface.Surface π F hBranch a.2) := borel _
local instance (a : Base A) : BorelSpace (BeltramiMarkedFiberSurface.Surface π F hBranch a.2) := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (transformed q (D n)) (fiberForm π F hBranch (p n)))

def homeomorph (n : ℕ) : Z ≃ₜ BeltramiMarkedFiberSurface.Surface π F hBranch (p n).2 :=
  (toOriginal q (D n)).symm.trans (e n).homeomorph

theorem measurePreserving (n : ℕ) : MeasurePreserving (homeomorph π F hBranch q D p e n)
    (MNEC.NativePhysicalArea.surfaceArea q) (MNEC.NativePhysicalArea.surfaceArea (fiberForm π F hBranch (p n))) :=
  (MNEC.NativeDifferentialEquivArea.homeomorph_surfaceArea_measurePreserving (e n)).comp
    (NativeDeformationArea.surface_measurePreserving q (D n))

theorem conull_limit_density (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀))
    (hzero : ∀ i, p₀.2.val.2 i = 0) {E : Set Z} (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (x₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) (hx₀ : x₀ ∈ regularSet (fiberForm π F hBranch p₀))
    {W : Set (Total π F hBranch)} (hW : IsOpen W) (hxW : inclusion π F hBranch p₀ x₀ ∈ W) :
    ∃ z ∈ E, ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y ∈ W ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n)) (homeomorph π F hBranch q D p e (σ n) z)) atTop
          (𝓝 (inclusion π F hBranch p₀ y)) := by
  let : IsFiniteMeasure (MNEC.NativePhysicalArea.surfaceArea q) := MNEC.NativeProbabilityArea.surfaceArea_isFinite q
  exact BeltramiMarkedConullLimitDensity.density_regular π F hBranch (MNEC.NativePhysicalArea.surfaceArea q)
    p p₀ hp hzero (fun n => homeomorph π F hBranch q D p e n)
    (fun n => (homeomorph π F hBranch q D p e n).continuous) (measurePreserving π F hBranch q D p e)
    hE x₀ hx₀ hW hxW

end VeechDichotomy.BeltramiMarkedSL2SourceMaps
