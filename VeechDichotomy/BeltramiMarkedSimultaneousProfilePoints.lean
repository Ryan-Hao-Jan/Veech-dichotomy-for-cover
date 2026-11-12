module

public import VeechDichotomy.BeltramiMarkedNativePointValues
public import VeechDichotomy.BeltramiMarkedSimultaneousLimits

/-! Finitely many actual target neighborhoods admit fixed complete
source points carrying the already proved conull source property, with
regular image limits on ONE common further subsequence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedSimultaneousProfilePoints

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff

variable {X Y Z I : Type*} [Finite I]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

theorem common_subsequence (P : CompleteOrbits q v → Prop) (E : Set Z)
    (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ P x)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (x₀ : I → BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : ∀ i, x₀ i ∈ regularSet (fiberForm π F hBranch p₀))
    (W : I → Set (Total π F hBranch)) (hW : ∀ i, IsOpen (W i))
    (hxW : ∀ i, inclusion π F hBranch p₀ (x₀ i) ∈ W i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i, ∃ z : CompleteOrbits q v, P z ∧
      ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
        y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y ∈ W i ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e z.val (σ n)).val)
          atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  obtain ⟨σ, hσ, hsim⟩ := BeltramiMarkedSimultaneousLimits.common_subsequence π F hBranch q
    (fun n => NativeTeichmullerRay.matrix v hv (t n)) p e p₀ hp hzero hE x₀ hx₀ W hW hxW
  refine ⟨σ, hσ, ?_⟩
  intro i
  obtain ⟨w, hw, y, hyreg, hyW, hlim⟩ := hsim i
  obtain ⟨z, hzw, hzP⟩ := hEP w hw
  change z.val.val = w at hzw
  refine ⟨z, hzP, y, hyreg, hyW, ?_⟩
  have heq (n : ℕ) : (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e z.val (σ n)).val =
      BeltramiMarkedSL2SourceMaps.homeomorph π F hBranch q (fun n => NativeTeichmullerRay.matrix v hv (t n)) p e (σ n) w := by
    rw [BeltramiMarkedNativePointValues.point_value, hzw]
  simpa only [heq] using hlim

end VeechDichotomy.BeltramiMarkedSimultaneousProfilePoints
