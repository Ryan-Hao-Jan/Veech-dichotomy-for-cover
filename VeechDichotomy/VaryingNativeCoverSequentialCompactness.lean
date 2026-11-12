module

public import VeechDichotomy.VaryingNativeCoverExhaustion
public import VeechDichotomy.CompactFiniteLabels

/-! One actual proper holomorphic family contains a subsequence of
the varying-base native source curves when their concrete parameters
converge. All source comparisons are genuine native differential
equivalences commuting with the actual base identification. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingNativeCoverSequentialCompactness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters VaryingNativeCoverExhaustion
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} (Y : ℕ → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {q : Differential X} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (A : Data q b μ₀) (F : Family A) (L : ℕ → SL2) (u : ℕ → Fin m → X)
  (hvalid : ∀ i, Valid A (SL2BeltramiParameters.parameter (L i)) (u i)) (r : ∀ i, Differential (Y i))

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (ρ : ∀ i, Cover (transformed q (L i)) (r i))
  (hbranch : ∀ i, branchValues (ρ i) = range (fun k => (toOriginal q (L i)).symm (u i k)))

theorem subsequence_of_tendsto {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (ρ i) = d)
    {v : BeltramiMarkedScaledFamily.Base A}
    (hparam : Tendsto (fun n => familyParameters A (L n) (u n) (hvalid n)) atTop (𝓝 v)) :
    ∃ j : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => familyParameters A (L (σ n)) (u (σ n)) (hvalid (σ n))) atTop (𝓝 v) ∧
      ∀ n, ∃ e : MNEC.NativeDifferentialEquiv.Equiv (r (σ n))
        (familyDifferential Y A F L u hvalid r ρ hbranch j (familyParameters A (L (σ n)) (u (σ n)) (hvalid (σ n)))),
        ∀ y, (familyCover Y A F L u hvalid r ρ hbranch j (familyParameters A (L (σ n)) (u (σ n)) (hvalid (σ n)))).map
          (e.homeomorph y) = (baseEquivalence A (L (σ n)) (u (σ n)) (hvalid (σ n))).homeomorph ((ρ (σ n)).map y) := by
  classical
  obtain ⟨J, hJ, hexhaust⟩ := finite_analytic_exhaustion Y A F L u hvalid r ρ hbranch hdegree
  choose j hj e he using hexhaust
  let : Finite J := hJ.to_subtype
  let label (n : ℕ) : J := ⟨j n, hj n⟩
  obtain ⟨j₀, σ, hσ, hlabel⟩ := CompactFiniteLabels.constant_subsequence label
  refine ⟨j₀.val, σ, hσ, hparam.comp hσ.tendsto_atTop, ?_⟩
  intro n
  have hindex : j (σ n) = j₀.val := congrArg Subtype.val (hlabel n)
  have hwitness : ∃ f : MNEC.NativeDifferentialEquiv.Equiv (r (σ n))
      (familyDifferential Y A F L u hvalid r ρ hbranch (j (σ n)) (familyParameters A (L (σ n)) (u (σ n)) (hvalid (σ n)))),
      ∀ y, (familyCover Y A F L u hvalid r ρ hbranch (j (σ n)) (familyParameters A (L (σ n)) (u (σ n)) (hvalid (σ n)))).map
        (f.homeomorph y) = (baseEquivalence A (L (σ n)) (u (σ n)) (hvalid (σ n))).homeomorph ((ρ (σ n)).map y) :=
    ⟨e (σ n), he (σ n)⟩
  exact hindex ▸ hwitness

theorem limit_degree (j : ℕ) (v : BeltramiMarkedScaledFamily.Base A) :
    NativeFullCoverDegree.degree (familyCover Y A F L u hvalid r ρ hbranch j v) = NativeFullCoverDegree.degree (ρ j) :=
  (BeltramiMarkedScaledFamily.degree_eq (fixedCover Y A F L u hvalid r ρ hbranch j) F
    (fixedBranch Y A F L u hvalid r ρ hbranch j) v).trans
      (VaryingNativeCoverFiniteness.degree_eq Y A F L u hvalid r ρ hbranch j)

end VeechDichotomy.VaryingNativeCoverSequentialCompactness
