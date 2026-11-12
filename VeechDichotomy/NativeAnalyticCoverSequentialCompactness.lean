module

public import VeechDichotomy.NativeAnalyticCoverExhaustion
public import VeechDichotomy.CompactFiniteLabels

/-! Actual local sequential compactness of fixed-degree native covers:
after passing to a subsequence, one constructed analytic family contains
all sources, preserving their native differentials and covering maps,
and its complex parameters converge to an actual native cover fiber.
No ambient moduli topology or Hurwitz properness premise is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverSequentialCompactness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters NativeAnalyticCoverExhaustion Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} (Y : ℕ → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))
variable {m : ℕ} (b : Fin m → X) (A : Data b) (a : ℕ → Parameters m)
variable (hBranch : ∀ i, branchValues (π i) = range (A.tuple (a i)).val)

theorem subsequence {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d)
    {K : Set (Parameters m)} (hK : IsCompact K) (ha : ∀ n, a n ∈ K) :
    ∃ j : ℕ, ∃ v ∈ K, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 v) ∧
      ∀ n, ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY (σ n))
        (familyDifferential Y ωY π b A a hBranch j (a (σ n))),
        ∀ y, (familyCover Y ωY π b A a hBranch j (a (σ n))).map (e.homeomorph y) = (π (σ n)).map y := by
  classical
  obtain ⟨J, hJ, hexhaust⟩ := finite_analytic_exhaustion Y ωY π b A a hBranch hdegree
  choose j hj e he using hexhaust
  let : Finite J := hJ.to_subtype
  let label (n : ℕ) : J := ⟨j n, hj n⟩
  obtain ⟨j₀, v, hv, σ, hσ, hconv, hlabel⟩ := CompactFiniteLabels.subsequence hK a ha label
  refine ⟨j₀.val, v, hv, σ, hσ, hconv, ?_⟩
  intro n
  have hindex : j (σ n) = j₀.val := congrArg Subtype.val (hlabel n)
  have hwitness : ∃ f : MNEC.NativeDifferentialEquiv.Equiv (ωY (σ n))
      (familyDifferential Y ωY π b A a hBranch (j (σ n)) (a (σ n))),
      ∀ y, (familyCover Y ωY π b A a hBranch (j (σ n)) (a (σ n))).map (f.homeomorph y) = (π (σ n)).map y :=
    ⟨e (σ n), he (σ n)⟩
  exact hindex ▸ hwitness

theorem subsequence_of_tendsto {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d)
    {v : Parameters m} (ha : Tendsto a atTop (𝓝 v)) :
    ∃ j : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 v) ∧
      ∀ n, ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY (σ n))
        (familyDifferential Y ωY π b A a hBranch j (a (σ n))),
        ∀ y, (familyCover Y ωY π b A a hBranch j (a (σ n))).map (e.homeomorph y) = (π (σ n)).map y := by
  classical
  obtain ⟨J, hJ, hexhaust⟩ := finite_analytic_exhaustion Y ωY π b A a hBranch hdegree
  choose j hj e he using hexhaust
  let : Finite J := hJ.to_subtype
  let label (n : ℕ) : J := ⟨j n, hj n⟩
  obtain ⟨j₀, σ, hσ, hlabel⟩ := CompactFiniteLabels.constant_subsequence label
  refine ⟨j₀.val, σ, hσ, ha.comp hσ.tendsto_atTop, ?_⟩
  intro n
  have hindex : j (σ n) = j₀.val := congrArg Subtype.val (hlabel n)
  have hwitness : ∃ f : MNEC.NativeDifferentialEquiv.Equiv (ωY (σ n))
      (familyDifferential Y ωY π b A a hBranch (j (σ n)) (a (σ n))),
      ∀ y, (familyCover Y ωY π b A a hBranch (j (σ n)) (a (σ n))).map (f.homeomorph y) = (π (σ n)).map y :=
    ⟨e (σ n), he (σ n)⟩
  exact hindex ▸ hwitness

theorem limit_degree (j : ℕ) (v : Parameters m) :
    NativeFullCoverDegree.degree (familyCover Y ωY π b A a hBranch j v) = NativeFullCoverDegree.degree (π j) := by
  calc
    NativeFullCoverDegree.degree (familyCover Y ωY π b A a hBranch j v) =
        NativeFullCoverDegree.degree (fixedCover Y ωY π b A a hBranch j) :=
      RelocatedCoverDegree.degree_eq _ _ _ _
    _ = NativeFullCoverDegree.degree (π j) :=
      NativeLocalCoverPullback.degree_eq Y ωY π b A.marks (fun i => A.tuple (a i)) hBranch j

theorem limit_branch_values (j : ℕ) (v : Parameters m) :
    branchValues (familyCover Y ωY π b A a hBranch j v) = range (A.tuple v).val :=
  NativeLocalCoverFamily.branch_values _ _ _ _ _

end VeechDichotomy.NativeAnalyticCoverSequentialCompactness
