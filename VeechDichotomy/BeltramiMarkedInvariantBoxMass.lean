module

public import VeechDichotomy.BeltramiMarkedUniversalMeanEquality
public import VeechDichotomy.NativeConullPhaseProperties

/-! Every tested actual native invariant probability has the SAME
concrete flowbox masses as actual normalized area along the returning
family. Actual common source/test profiles, universal mean comparison
and the proved mean-integral identities discharge the measure step.
The tested probability may be singular; ergodicity is not assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedInvariantBoxMass

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
theorem mass_eq (hmin : NativeDynamics.MinimalDirection q vertical)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0) (ht : Tendsto t atTop atTop)
    (ν : Measure (CompleteOrbits q vertical)) (hν : NativeDynamics.InvariantProbability q vertical ν)
    (D : NativeBufferedFlowboxes.Data q) : ν D.phaseRegion = normalizedCompleteArea q vertical D.phaseRegion := by
  let μA := normalizedCompleteArea q vertical
  have hA : NativeDynamics.InvariantProbability q vertical μA := NativeDynamics.area_invariantProbability q vertical hmin.1
  let : IsProbabilityMeasure μA := hA.1
  let : IsProbabilityMeasure ν := hν.1
  let R : ℕ → ℝ := fun n => NativeRayReferenceTimes.reference vertical (t n)
  have hR : Tendsto R atTop atTop := NativeRayReferenceTimes.reference_tendsto vertical hv ht
  obtain ⟨σ, hσ, E, hE, harea, htest⟩ := NativeFlowboxProfileSets.source_and_test q hmin ν hν (fun _ => D) R hR
  let mA := fun x => NativeIndicatorMeanProfiles.mean q vertical μA hA D.phaseRegion D.phaseRegion_open.measurableSet false x
  let mν := fun x => NativeIndicatorMeanProfiles.mean q vertical ν hν D.phaseRegion D.phaseRegion_open.measurableSet false x
  have hEParea : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      NativeFlowboxProfileSets.FullProfile q D (R ∘ σ) z (mA z) := by
    intro w hw
    obtain ⟨z, hzw, hzp⟩ := harea w hw
    exact ⟨z, hzw, hzp 0⟩
  have hEP : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D (R ∘ σ) z mz := by
    intro w hw
    obtain ⟨z, hzw, hzp⟩ := hEParea w hw
    exact ⟨z, hzw, mA z, hzp⟩
  have haeA : ∀ᵐ x ∂μA, NativeFlowboxProfileSets.FullProfile q D (R ∘ σ) x (mA x) :=
    NativeConullPhaseProperties.of_conull_set q vertical hmin.1 _ E hE hEParea
  obtain ⟨anchor, hanchor⟩ := haeA.exists
  let c := mA anchor
  have hareaConst : ∀ᵐ x ∂μA, mA x = c := by
    filter_upwards [haeA] with x hx
    exact BeltramiMarkedUniversalMeanEquality.mean_eq π F hBranch q hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k))
      D hmin p₀ (hp.comp hσ.tendsto_atTop) hzero E hE hEP (ht.comp hσ.tendsto_atTop) x anchor hx hanchor
  have htestConst : ∀ᵐ x ∂ν, mν x = c := by
    filter_upwards [htest] with x hx
    exact BeltramiMarkedUniversalMeanEquality.mean_eq π F hBranch q hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k))
      D hmin p₀ (hp.comp hσ.tendsto_atTop) hzero E hE hEP (ht.comp hσ.tendsto_atTop) x anchor (hx 0) hanchor
  have hAmass : (μA D.phaseRegion).toReal = c := by
    rw [← NativeIndicatorMeanProfiles.integral_mean q vertical μA hA D.phaseRegion D.phaseRegion_open.measurableSet false]
    calc
      (∫ x, NativeIndicatorMeanProfiles.mean q vertical μA hA D.phaseRegion D.phaseRegion_open.measurableSet false x ∂μA) =
          ∫ _ : CompleteOrbits q vertical, c ∂μA := integral_congr_ae hareaConst
      _ = c := by simp
  have hνmass : (ν D.phaseRegion).toReal = c := by
    rw [← NativeIndicatorMeanProfiles.integral_mean q vertical ν hν D.phaseRegion D.phaseRegion_open.measurableSet false]
    calc
      (∫ x, NativeIndicatorMeanProfiles.mean q vertical ν hν D.phaseRegion D.phaseRegion_open.measurableSet false x ∂ν) =
          ∫ _ : CompleteOrbits q vertical, c ∂ν := integral_congr_ae htestConst
      _ = c := by simp
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν D.phaseRegion) (measure_ne_top μA D.phaseRegion)).mp
    (hνmass.trans hAmass.symm)

end VeechDichotomy.BeltramiMarkedInvariantBoxMass
