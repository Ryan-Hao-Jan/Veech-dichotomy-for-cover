module

public import VeechDichotomy.VaryingNativeCoverFiniteness
public import VeechDichotomy.BeltramiMarkedScaledEmbeddings

/-! Finitely many CONSTRUCTED proper holomorphic families exhaust the
actual varying-base, varying-branch native covers. Normalized native cover
equivalences reconstruct explicit whole-source homeomorphisms; commuting
native covers prove holomorphicity and preservation of the true forms. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingNativeCoverExhaustion

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters
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

abbrev fixedCover := VaryingNativeCoverFiniteness.cover Y A F L u hvalid r ρ hbranch
abbrev fixedDifferential := VaryingNativeCoverFiniteness.differential Y A F L u hvalid r ρ hbranch

theorem fixedBranch (j : ι) : range b = branchValues (fixedCover Y A F L u hvalid r ρ hbranch j) :=
  (VaryingNativeCoverFiniteness.branch_values Y A F L u hvalid r ρ hbranch j).symm

abbrev FamilySource (j : ι) (p : BeltramiMarkedScaledFamily.Base A) :=
  BeltramiMarkedFiberSurface.Surface (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p.2

def familyDifferential (j : ι) (p : BeltramiMarkedScaledFamily.Base A) : Differential (FamilySource Y A F L u hvalid r ρ hbranch j p) :=
  BeltramiMarkedScaledFamily.fiberForm (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p

def familyCover (j : ι) (p : BeltramiMarkedScaledFamily.Base A) :
    Cover (BeltramiMarkedScaledFamily.baseFiberForm p) (familyDifferential Y A F L u hvalid r ρ hbranch j p) :=
  BeltramiMarkedScaledFamily.cover (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) p

abbrev FamilyTotal (j : ι) := BeltramiMarkedScaledFamily.Total (fixedCover Y A F L u hvalid r ρ hbranch j) F
  (fixedBranch Y A F L u hvalid r ρ hbranch j)

def reconstructionHomeomorph {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv (fixedDifferential Y A F L u hvalid r ρ hbranch i)
      (fixedDifferential Y A F L u hvalid r ρ hbranch j)) :
    Y i ≃ₜ FamilySource Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i)) :=
  ((VaryingNativeCoverPullback.fromOriginal A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)).trans e.homeomorph).trans
    (BeltramiMarkedFiberSurface.toOriginal (fixedCover Y A F L u hvalid r ρ hbranch j) F
      (fixedBranch Y A F L u hvalid r ρ hbranch j) (markParameters A (L i) (u i) (hvalid i))).symm

theorem reconstruction_square {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv (fixedDifferential Y A F L u hvalid r ρ hbranch i)
      (fixedDifferential Y A F L u hvalid r ρ hbranch j))
    (he : ∀ z, (fixedCover Y A F L u hvalid r ρ hbranch j).map (e.homeomorph z) =
      (fixedCover Y A F L u hvalid r ρ hbranch i).map z) (y : Y i) :
    (familyCover Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i))).map
      (reconstructionHomeomorph Y A F L u hvalid r ρ hbranch e y) =
        (baseEquivalence A (L i) (u i) (hvalid i)).homeomorph ((ρ i).map y) := by
  apply (NativeBeltramiSurface.toOriginal q (SL2BeltramiParameters.parameter (L i))).injective
  change BeltramiMarkedBaseTransport.transported F (markParameters A (L i) (u i) (hvalid i))
    ((fixedCover Y A F L u hvalid r ρ hbranch j).map
      (e.homeomorph (VaryingNativeCoverPullback.fromOriginal A F (L i) (u i) (hvalid i) (ρ i) (hbranch i) y))) = ((ρ i).map y).point
  rw [he, VaryingNativeCoverPullback.normalized_map_value, Homeomorph.apply_symm_apply]

def reconstruction {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv (fixedDifferential Y A F L u hvalid r ρ hbranch i)
      (fixedDifferential Y A F L u hvalid r ρ hbranch j))
    (he : ∀ z, (fixedCover Y A F L u hvalid r ρ hbranch j).map (e.homeomorph z) =
      (fixedCover Y A F L u hvalid r ρ hbranch i).map z) :
    MNEC.NativeDifferentialEquiv.Equiv (r i)
      (familyDifferential Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i))) :=
  NativeCoverIsomorphism.equivalence_of_commutes (VaryingNativeCoverPullback.nativeCover A (L i) (u i) (hvalid i) (ρ i))
    (familyCover Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i)))
    (reconstructionHomeomorph Y A F L u hvalid r ρ hbranch e) (reconstruction_square Y A F L u hvalid r ρ hbranch e he)

theorem finite_analytic_exhaustion {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (ρ i) = d) :
    ∃ J : Set ι, J.Finite ∧ ∀ i, ∃ j ∈ J,
      ∃ e : MNEC.NativeDifferentialEquiv.Equiv (r i)
        (familyDifferential Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i))),
        ∀ y, (familyCover Y A F L u hvalid r ρ hbranch j (familyParameters A (L i) (u i) (hvalid i))).map
          (e.homeomorph y) = (baseEquivalence A (L i) (u i) (hvalid i)).homeomorph ((ρ i).map y) := by
  obtain ⟨J, hJ, hrep⟩ := VaryingNativeCoverFiniteness.finite_representatives Y A F L u hvalid r ρ hbranch hdegree
  refine ⟨J, hJ, ?_⟩
  intro i
  obtain ⟨j, hj, e, he⟩ := hrep i
  exact ⟨j, hj, reconstruction Y A F L u hvalid r ρ hbranch e he,
    reconstruction_square Y A F L u hvalid r ρ hbranch e he⟩

end VeechDichotomy.VaryingNativeCoverExhaustion
