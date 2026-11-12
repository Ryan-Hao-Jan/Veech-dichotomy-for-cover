module

public import VeechDichotomy.BeltramiMarkedNativePointValues
public import VeechDichotomy.ProperFiberLimits

/-! Every specified source point has a subsequential actual image limit
in the exact native limit fiber. Properness supplies this deterministic
pointwise compactness without a positive-mass or genericity hypothesis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedPointCompactness

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
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
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

theorem subsequence (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (x : Regular q) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      Tendsto (fun n => inclusion π F hBranch (p (σ n))
        (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x (σ n)).val)
        atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  let : SecondCountableTopology Y := ChartedSpace.secondCountable_of_sigmaCompact ℂ Y
  let : SecondCountableTopology (BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch) :=
    (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).isEmbedding.secondCountableTopology
  let f := fun n => inclusion π F hBranch (p n) (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x n).val
  have hproj : Tendsto (fun n => projection π F hBranch (f n)) atTop (𝓝 p₀) := by
    simpa only [f, projection_inclusion] using hp
  obtain ⟨y, hy, σ, hσ, hlim⟩ := ProperFiberLimits.subsequence (projection π F hBranch) (proper_projection π F hBranch) f p₀ hproj
  let y₀ := (fiberHomeomorph π F hBranch p₀).symm ⟨y, hy⟩
  have heq : inclusion π F hBranch p₀ y₀ = y :=
    congrArg Subtype.val ((fiberHomeomorph π F hBranch p₀).apply_symm_apply ⟨y, hy⟩)
  refine ⟨σ, hσ, y₀, ?_⟩
  rw [heq]
  exact hlim

end VeechDichotomy.BeltramiMarkedPointCompactness
