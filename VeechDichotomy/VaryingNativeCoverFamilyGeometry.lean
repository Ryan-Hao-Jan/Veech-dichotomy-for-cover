module

public import VeechDichotomy.VaryingNativeCoverExhaustion

/-! Explicit geometry of the ACTUAL constructed families appearing
in native cover compactness. Their parameter projections are proper
holomorphic submersions. Every genuine native source comparison gives
a holomorphic topological embedding onto the ENTIRE projection fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingNativeCoverFamilyGeometry

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters VaryingNativeCoverExhaustion
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {q : Differential X} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (A : Data q b μ₀) (F : Family A) (L : ι → SL2) (u : ι → Fin m → X)
  (hvalid : ∀ i, Valid A (SL2BeltramiParameters.parameter (L i)) (u i)) (r : ∀ i, Differential (Y i))

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (ρ : ∀ i, Cover (transformed q (L i)) (r i))
  (hbranch : ∀ i, branchValues (ρ i) = range (fun k => (toOriginal q (L i)).symm (u i k)))

def projection (j : ι) : FamilyTotal Y A F L u hvalid r ρ hbranch j → BeltramiMarkedScaledFamily.Base A :=
  BeltramiMarkedScaledFamily.projection (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j)

theorem proper_projection (j : ι) : IsProperMap (projection Y A F L u hvalid r ρ hbranch j) :=
  BeltramiMarkedScaledFamily.proper_projection (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j)

theorem holomorphic_projection (j : ι) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))) ω (projection Y A F L u hvalid r ρ hbranch j) :=
  BeltramiMarkedScaledFamily.projection_holomorphic (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j)

theorem projection_surjective_derivative (j : ι) (z : FamilyTotal Y A F L u hvalid r ρ hbranch j) :
    Function.Surjective (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))) (projection Y A F L u hvalid r ρ hbranch j) z) :=
  BeltramiMarkedScaledFamily.projection_surjective_derivative (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) z

variable {i : ι} (j : ι) (p : BeltramiMarkedScaledFamily.Base A)
  (e : MNEC.NativeDifferentialEquiv.Equiv (r i) (familyDifferential Y A F L u hvalid r ρ hbranch j p))

def embedding : Y i → FamilyTotal Y A F L u hvalid r ρ hbranch j :=
  BeltramiMarkedScaledEmbeddings.embedding (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p e

def fiberHomeomorph : Y i ≃ₜ (projection Y A F L u hvalid r ρ hbranch j ⁻¹' {p}) :=
  BeltramiMarkedScaledEmbeddings.fiberHomeomorph (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p e

theorem holomorphic_embedding : ContMDiff 𝓘(ℂ)
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) ω (embedding Y A F L u hvalid r ρ hbranch j p e) :=
  BeltramiMarkedScaledEmbeddings.holomorphic_embedding (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p e

theorem isEmbedding_embedding : IsEmbedding (embedding Y A F L u hvalid r ρ hbranch j p e) :=
  IsEmbedding.subtypeVal.comp (fiberHomeomorph Y A F L u hvalid r ρ hbranch j p e).isEmbedding

theorem projection_embedding (y : Y i) :
    projection Y A F L u hvalid r ρ hbranch j (embedding Y A F L u hvalid r ρ hbranch j p e y) = p := rfl

theorem embedding_range : range (embedding Y A F L u hvalid r ρ hbranch j p e) =
    projection Y A F L u hvalid r ρ hbranch j ⁻¹' {p} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hz
    obtain ⟨y, hy⟩ := (fiberHomeomorph Y A F L u hvalid r ρ hbranch j p e).surjective ⟨z, hz⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem differential_pullback : Jacobians.pullbackForm e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (familyDifferential Y A F L u hvalid r ρ hbranch j p).val = (r i).val :=
  BeltramiMarkedScaledEmbeddings.differential_pullback (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p e

end VeechDichotomy.VaryingNativeCoverFamilyGeometry
