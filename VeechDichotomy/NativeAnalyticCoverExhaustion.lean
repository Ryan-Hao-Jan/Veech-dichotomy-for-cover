module

public import VeechDichotomy.NativeAnalyticCoverEmbeddings
public import VeechDichotomy.NativeLocalCoverExhaustion

/-! Finitely many CONSTRUCTED analytic families exhaust an arbitrary
fixed-degree native cover family over nearby branch configurations. The
comparisons commute with the covering maps and preserve actual native
differentials. This uses monodromy finiteness, not a Hurwitz properness input. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverExhaustion

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))
variable {m : ℕ} (b : Fin m → X) (A : Data b) (a : ι → Parameters m)
variable (hBranch : ∀ i, branchValues (π i) = range (A.tuple (a i)).val)

abbrev fixedCover := NativeLocalCoverExhaustion.fixedCover Y ωY π b A.marks (fun i => A.tuple (a i)) hBranch

theorem fixedBranch (j : ι) : range b = branchValues (fixedCover Y ωY π b A a hBranch j) :=
  (NativeLocalCoverPullback.branch_values Y ωY π b A.marks (fun i => A.tuple (a i)) hBranch j).symm

abbrev FamilySource (j : ι) (v : Parameters m) :=
  NativeAnalyticCoverFiberCharts.Source (fixedCover Y ωY π b A a hBranch j) b
    (fixedBranch Y ωY π b A a hBranch j) A v

def familyDifferential (j : ι) (v : Parameters m) : Differential (FamilySource Y ωY π b A a hBranch j v) :=
  NativeLocalCoverFamily.differential (fixedCover Y ωY π b A a hBranch j) b
    (fixedBranch Y ωY π b A a hBranch j) A.marks (A.tuple v)

def familyCover (j : ι) (v : Parameters m) : Cover ωX (familyDifferential Y ωY π b A a hBranch j v) :=
  NativeLocalCoverFamily.cover (fixedCover Y ωY π b A a hBranch j) b
    (fixedBranch Y ωY π b A a hBranch j) A.marks (A.tuple v)

abbrev FamilyTotal (j : ι) := NativeAnalyticCoverTotalSpace.TotalSpace
  (fixedCover Y ωY π b A a hBranch j) A (fixedBranch Y ωY π b A a hBranch j)

def familyForm (j : ι) : HolomorphicCotangentForms.Form (Space m × ℂ) (FamilyTotal Y ωY π b A a hBranch j) :=
  NativeAnalyticCoverForm.form (fixedCover Y ωY π b A a hBranch j) A (fixedBranch Y ωY π b A a hBranch j)

theorem finite_analytic_exhaustion {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d) :
    ∃ J : Set ι, J.Finite ∧ ∀ i, ∃ j ∈ J,
      ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY i) (familyDifferential Y ωY π b A a hBranch j (a i)),
        ∀ y, (familyCover Y ωY π b A a hBranch j (a i)).map (e.homeomorph y) = (π i).map y :=
  NativeLocalCoverExhaustion.finite_local_exhaustion Y ωY π b A.marks (fun i => A.tuple (a i)) hBranch hdegree

end VeechDichotomy.NativeAnalyticCoverExhaustion
