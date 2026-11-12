module

public import VeechDichotomy.BeltramiMarkedLimitRectangles
public import VeechDichotomy.BeltramiMarkedUnrestrictedLocalMeans

/-! The unrestricted native local mean theorem applied to a concrete
good family rectangle. Its positive interior height interval is chosen
from the actual rectangle dimensions, rather than supplied as extra data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRectangleLocalMeans

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiMarkedLimitRectangles
open BeltramiMarkedShiftedSourcePoints
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
local notation "P" => point π F hBranch q vertical hv t p e
local notation "R" => (fun n => NativeRayReferenceTimes.reference vertical (t n))

theorem mean_eq (D : NativeBufferedFlowboxes.Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (E : Set Z) (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D R z mz)
    (B : Rectangle π F hBranch p₀) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hxB : x₀ ∈ B.region) (hyB : y₀ ∈ B.region)
    (x y : CompleteOrbits q vertical) (dx dy : ℕ → ℝ) {dx₀ dy₀ : ℝ}
    (hdx : Tendsto dx atTop (𝓝 dx₀)) (hdy : Tendsto dy atTop (𝓝 dy₀))
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (P x dx n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (P y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀)))
    (ht : Tendsto t atTop atTop) {mx my : ℝ}
    (hpx : NativeFlowboxProfileSets.FullProfile q D R x mx)
    (hpy : NativeFlowboxProfileSets.FullProfile q D R y my) : mx = my := by
  exact BeltramiMarkedUnrestrictedLocalMeans.mean_eq π F hBranch q hv t p e D hmin p₀ hp hzero E hE hEP
    B.slice B.not_critical B.base_regular x₀ y₀ hxB.1 hyB.1 B.target hxB.2 hyB.2 x y dx dy hdx hdy
    ((2 * B.bottom + B.top) / 3) ((B.bottom + 2 * B.top) / 3)
    (by linarith [B.height_pos]) (by linarith [B.height_pos]) (by linarith [B.height_pos]) hx hy ht hpx hpy

end VeechDichotomy.BeltramiMarkedRectangleLocalMeans
