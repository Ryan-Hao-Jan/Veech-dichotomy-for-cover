module

public import VeechDichotomy.BeltramiMarkedInvariantBoxMass
public import VeechDichotomy.NativeFlowboxMeasureExt

/-! A proved native family version of Masur's criterion for the
unit-vertical source direction. Actual returning ray equivalences into
the constructed proper family, with a zero-displacement limit, imply
unique ergodicity of the actual complete minimal native directional flow.
Every invariant probability is identified with actual normalized area. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFamilyMasurCriterion

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory
open NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (hv : vertical ≠ (0 : Plane)) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q vertical hv (t n)) (fiberForm π F hBranch (p n)))

include π F hBranch hv e in
theorem uniquely_ergodic (hmin : NativeDynamics.MinimalDirection q vertical)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (ht : Tendsto t atTop atTop) : NativeDynamics.UniquelyErgodicDirection q vertical := by
  refine ⟨hmin.1, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hν.1
  apply NativeFlowboxMeasureExt.ext q ν (normalizedCompleteArea q vertical)
  intro D
  exact BeltramiMarkedInvariantBoxMass.mass_eq π F hBranch q hv t p e hmin p₀ hp hzero ht ν hν D

end VeechDichotomy.NativeFamilyMasurCriterion
