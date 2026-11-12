module

public import VeechDichotomy.BeltramiMarkedRegularTranslatedLimits
public import VeechDichotomy.BeltramiMarkedGlobalRegularMeans

/-! Actual source flowbox FullProfile means are equal for ANY two fixed
complete source points along the returning native family. Regular image
limits are now CONSTRUCTED by properness and native primitive escape;
they are no longer hypotheses of the statistical comparison theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedUniversalMeanEquality

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
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
local notation "R" => (fun n => NativeRayReferenceTimes.reference vertical (t n))

include π F hBranch hv e in
theorem mean_eq (D : NativeBufferedFlowboxes.Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (E : Set Z) (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D R z mz)
    (ht : Tendsto t atTop atTop) (x y : CompleteOrbits q vertical) {mx my : ℝ}
    (hpx : NativeFlowboxProfileSets.FullProfile q D R x mx)
    (hpy : NativeFlowboxProfileSets.FullProfile q D R y my) : mx = my := by
  obtain ⟨σ, hσ, dx, dx₀, hdx, x₀, hx⟩ := BeltramiMarkedRegularTranslatedLimits.exists_regular_limit π F hBranch
    q vertical hv t p e p₀ hp x
  obtain ⟨τ, hτ, dy, dy₀, hdy, y₀, hy⟩ := BeltramiMarkedRegularTranslatedLimits.exists_regular_limit π F hBranch
    q vertical hv (t ∘ σ) (p ∘ σ) (fun n => e (σ n)) p₀ (hp.comp hσ.tendsto_atTop) y
  have hmono : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hclock : Tendsto R atTop atTop := NativeRayReferenceTimes.reference_tendsto vertical hv ht
  have hpx' := NativeFlowboxProfileSets.subsequence q D R hclock x mx hpx (σ ∘ τ) hmono
  have hpy' := NativeFlowboxProfileSets.subsequence q D R hclock y my hpy (σ ∘ τ) hmono
  have hEP' : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D (R ∘ (σ ∘ τ)) z mz := by
    intro w hw
    obtain ⟨z, hzw, mz, hzp⟩ := hEP w hw
    exact ⟨z, hzw, mz, NativeFlowboxProfileSets.subsequence q D R hclock z mz hzp (σ ∘ τ) hmono⟩
  have hx' : Tendsto (fun n => inclusion π F hBranch (p ((σ ∘ τ) n))
      (BeltramiMarkedShiftedSourcePoints.point π F hBranch q vertical hv (t ∘ (σ ∘ τ)) (p ∘ (σ ∘ τ))
        (fun k => e ((σ ∘ τ) k)) x (dx ∘ τ) n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀.val)) := by
    have heq (n : ℕ) :
        BeltramiMarkedShiftedSourcePoints.point π F hBranch q vertical hv (t ∘ (σ ∘ τ)) (p ∘ (σ ∘ τ))
          (fun k => e ((σ ∘ τ) k)) x (dx ∘ τ) n =
        BeltramiMarkedShiftedSourcePoints.point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ)
          (fun k => e (σ k)) x dx (τ n) := rfl
    simp_rw [heq]
    exact hx.comp hτ.tendsto_atTop
  have hy' : Tendsto (fun n => inclusion π F hBranch (p ((σ ∘ τ) n))
      (BeltramiMarkedShiftedSourcePoints.point π F hBranch q vertical hv (t ∘ (σ ∘ τ)) (p ∘ (σ ∘ τ))
        (fun k => e ((σ ∘ τ) k)) y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀.val)) := by
    simpa only [Function.comp_def] using hy
  exact BeltramiMarkedGlobalRegularMeans.mean_eq π F hBranch q hv (t ∘ (σ ∘ τ)) (p ∘ (σ ∘ τ))
    (fun k => e ((σ ∘ τ) k)) D hmin p₀ (hp.comp hmono.tendsto_atTop) hzero E hE hEP' x₀ y₀
    x y (dx ∘ τ) dy (hdx.comp hτ.tendsto_atTop) hdy hx' hy' (ht.comp hmono.tendsto_atTop) hpx' hpy'

end VeechDichotomy.BeltramiMarkedUniversalMeanEquality
