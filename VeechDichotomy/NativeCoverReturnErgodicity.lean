module

public import VeechDichotomy.NativeGeneralFamilyMasurCriterion
public import VeechDichotomy.NativeRayFamilyReturns

/-! Actual base quotient compact returns and compact invariant distinct
branch configurations imply unique ergodicity of every given minimal
source-cover direction. The previously proved concrete cover family
limit is unpacked into genuine native family objects and the proved
arbitrary-direction family criterion is applied to its actual ray maps. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverReturnErgodicity

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential NativeTranslationCover
open NativeDeformationRegular WholeDeformedAtlas LinearGroup NativeVeech BeltramiPlane
open UniformBeltramiMarkData UniformBeltramiMarkTransport UniformSL2ConfigurationParameters
open VaryingNativeCoverExhaustion Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y}

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qX B) := WholeDeformedAtlas.chartedSpace qX B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qX B) := WholeDeformedAtlas.isComplexManifold qX B ω
local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qY B) := WholeDeformedAtlas.chartedSpace qY B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qY B) := WholeDeformedAtlas.isComplexManifold qY B ω

theorem uniquely_ergodic (π : Cover qX qY) {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hCi : invariant (NativeAffineGroup.AffineGroup qX) C)
    (hbC : b ∈ C) (hconf : C ⊆ configuration m X) (v : Plane) (hv : v ≠ 0)
    (hmin : NativeDynamics.MinimalDirection qY v)
    (hreturns : HasCompactReturns (fun t =>
      (QuotientGroup.mk (NativeTeichmullerRay.matrix v hv t) : SL2 ⧸ derivativeGroup qX))) :
    NativeDynamics.UniquelyErgodicDirection qY v := by
  classical
  obtain ⟨t, _, ht, _, _, _, K, _, γ, φ, _, _, hfamily⟩ :=
    NativeRayFamilyReturns.from_returns π b hb hC hCi hbC hconf v hv hmin hreturns
  let Yseq := fun n => WholeSurface qY (NativeTeichmullerRay.matrix v hv (t n))
  let L := NativeNormalizedCoverSequences.matrix (NativeTeichmullerRay.matrix v hv ∘ t) γ
  let u := NativeNormalizedCoverSequences.branches b φ
  let r := fun n => NativeTeichmullerRay.rayForm qY v hv (t n)
  let ρ := NativeNormalizedCoverSequences.cover π (NativeTeichmullerRay.matrix v hv ∘ t) γ φ
  let hbranch := NativeNormalizedCoverSequences.branch_tuple π (NativeTeichmullerRay.matrix v hv ∘ t) γ φ b hb
  change NativeCoverFamilyLimits.FamilyLimit Yseq L u r ρ hbranch K C at hfamily
  obtain ⟨L₀, _, b₀, _, A, F, σ, hσ, hvalid, j, τ, hτ, hparam, hequiv⟩ := hfamily
  let πref := fixedCover (fun k => Yseq (σ k)) A F (L ∘ σ) (u ∘ σ) hvalid (fun k => r (σ k))
    (fun k => ρ (σ k)) (fun k => hbranch (σ k)) j
  let hbref := fixedBranch (fun k => Yseq (σ k)) A F (L ∘ σ) (u ∘ σ) hvalid (fun k => r (σ k))
    (fun k => ρ (σ k)) (fun k => hbranch (σ k)) j
  let p := fun n => familyParameters A (L (σ (τ n))) (u (σ (τ n))) (hvalid (τ n))
  let p₀ : BeltramiMarkedScaledFamily.Base A :=
    ((NativeSL2AnalyticFamily.parameters L₀).1, ComplexBeltramiMarkParameters.reference A)
  let T := fun n => t (σ (τ n))
  let e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm qY v hv (T n))
      (BeltramiMarkedScaledFamily.fiberForm πref F hbref (p n)) := fun n => (hequiv n).choose
  have hzero : ∀ i, p₀.2.val.2 i = 0 := fun _ => rfl
  have hT : Tendsto T atTop atTop := ht.comp (hσ.comp hτ).tendsto_atTop
  exact NativeGeneralFamilyMasurCriterion.uniquely_ergodic πref F hbref qY v hv T p e hmin p₀ hparam hzero hT

end VeechDichotomy.NativeCoverReturnErgodicity
