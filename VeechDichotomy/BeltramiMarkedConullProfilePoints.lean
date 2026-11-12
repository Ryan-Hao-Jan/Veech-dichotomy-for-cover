module

public import VeechDichotomy.BeltramiMarkedNativePointValues
public import VeechDichotomy.BeltramiMarkedRectangleNeighborhoods

/-! Select a FIXED complete source point carrying any property already
proved on a genuine area-conull source set, with a regular image limit
in a prescribed actual total-space neighborhood. This specializes to a
third comparison point avoiding two target horizontal coordinates. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedConullProfilePoints

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff

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
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

theorem point_with_property (P : CompleteOrbits q v → Prop) (E : Set Z)
    (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ P x)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (z₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hz₀ : z₀ ∈ regularSet (fiberForm π F hBranch p₀))
    {W : Set (Total π F hBranch)} (hW : IsOpen W) (hzW : inclusion π F hBranch p₀ z₀ ∈ W) :
    ∃ z : CompleteOrbits q v, P z ∧ ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      y ∈ regularSet (fiberForm π F hBranch p₀) ∧ inclusion π F hBranch p₀ y ∈ W ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e z.val (σ n)).val)
          atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  obtain ⟨w, hw, y, hyreg, hyW, σ, hσ, hlim⟩ := BeltramiMarkedSL2SourceMaps.conull_limit_density π F hBranch
    q (fun n => NativeTeichmullerRay.matrix v hv (t n)) p e p₀ hp hzero hE z₀ hz₀ hW hzW
  obtain ⟨z, hzw, hzP⟩ := hEP w hw
  change z.val.val = w at hzw
  refine ⟨z, hzP, y, hyreg, hyW, σ, hσ, ?_⟩
  have heq (n : ℕ) : (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e z.val (σ n)).val =
      BeltramiMarkedSL2SourceMaps.homeomorph π F hBranch q (fun n => NativeTeichmullerRay.matrix v hv (t n)) p e (σ n) w := by
    rw [BeltramiMarkedNativePointValues.point_value, hzw]
  simpa only [heq] using hlim

theorem point_in_rectangle (P : CompleteOrbits q v → Prop) (E : Set Z)
    (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ P x)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    {l r bot top : ℝ} (hlr : l < r) (hbt : bot < top)
    (hR : ∀ c ∈ Icc l r ×ˢ Icc bot top, toPlane.symm c ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (a b : ℝ) :
    ∃ z : CompleteOrbits q v, P z ∧ ∃ y : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2,
      y ∈ regularSet (fiberForm π F hBranch p₀) ∧
      inclusion π F hBranch p₀ y ∈ BeltramiMarkedRectangleNeighborhoods.region π F hBranch s l r bot top a b ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e z.val (σ n)).val)
          atTop (𝓝 (inclusion π F hBranch p₀ y)) := by
  obtain ⟨z₀, hzreg, hzW⟩ := BeltramiMarkedRectangleNeighborhoods.exists_regular_point π F hBranch s hs hreg p₀ hlr hbt hR a b
  exact point_with_property π F hBranch q v hv t p e P E hE hEP p₀ hp hzero z₀ hzreg
    (BeltramiMarkedRectangleNeighborhoods.region_open π F hBranch s l r bot top a b) hzW

end VeechDichotomy.BeltramiMarkedConullProfilePoints
