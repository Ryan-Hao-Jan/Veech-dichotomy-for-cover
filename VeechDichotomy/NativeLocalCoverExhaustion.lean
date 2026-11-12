module

public import VeechDichotomy.NativeLocalCoverPullback
public import VeechDichotomy.FiniteClassRepresentatives

/-! Finitely many actual local families exhaust an arbitrary fixed-degree
family of native covers whose ordered branch tuples lie in the constructed
configuration neighborhood. Every identification is a genuine holomorphic
differential equivalence commuting with the actual cover maps. This is a
set-theoretic exhaustion theorem; moduli continuity remains separate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverExhaustion

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeLocalCoverFamily
open Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))
variable {m : ℕ} (b : Fin m → X) (T : MarkTransport b) (u : ι → T.neighborhood)
variable (hBranch : ∀ i, branchValues (π i) = range (u i).val)

abbrev FixedSource := NativeLocalCoverPullback.Source Y ωY π b T u hBranch
abbrev fixedDifferential := NativeLocalCoverPullback.differential Y ωY π b T u hBranch
abbrev fixedCover := NativeLocalCoverPullback.cover Y ωY π b T u hBranch

abbrev FamilySource (j : ι) (v : T.neighborhood) :=
  NativeLocalCoverFamily.Source (fixedCover Y ωY π b T u hBranch j) b
    (NativeLocalCoverPullback.branch_values Y ωY π b T u hBranch j).symm T v

def familyDifferential (j : ι) (v : T.neighborhood) : Differential (FamilySource Y ωY π b T u hBranch j v) :=
  NativeLocalCoverFamily.differential (fixedCover Y ωY π b T u hBranch j) b
    (NativeLocalCoverPullback.branch_values Y ωY π b T u hBranch j).symm T v

def familyCover (j : ι) (v : T.neighborhood) : Cover ωX (familyDifferential Y ωY π b T u hBranch j v) :=
  NativeLocalCoverFamily.cover (fixedCover Y ωY π b T u hBranch j) b
    (NativeLocalCoverPullback.branch_values Y ωY π b T u hBranch j).symm T v

theorem family_branch_values (j : ι) (v : T.neighborhood) :
    branchValues (familyCover Y ωY π b T u hBranch j v) = range v.val :=
  NativeLocalCoverFamily.branch_values _ _ _ _ _

def reconstructionHomeomorph {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv
      (fixedDifferential Y ωY π b T u hBranch i) (fixedDifferential Y ωY π b T u hBranch j)) :
    Y i ≃ₜ FamilySource Y ωY π b T u hBranch j (u i) :=
  (((NativeLocalCoverPullback.toOriginal Y ωY π b T u hBranch i).symm).trans e.homeomorph).trans
    (NativeLocalCoverFamily.toOriginal (fixedCover Y ωY π b T u hBranch j) b
      (NativeLocalCoverPullback.branch_values Y ωY π b T u hBranch j).symm T (u i)).symm

theorem reconstruction_square {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv
      (fixedDifferential Y ωY π b T u hBranch i) (fixedDifferential Y ωY π b T u hBranch j))
    (he : ∀ z, (fixedCover Y ωY π b T u hBranch j).map (e.homeomorph z) =
      (fixedCover Y ωY π b T u hBranch i).map z) (y : Y i) :
    (familyCover Y ωY π b T u hBranch j (u i)).map
      (reconstructionHomeomorph Y ωY π b T u hBranch e y) = (π i).map y := by
  change T.transport (u i)
    ((fixedCover Y ωY π b T u hBranch j).map
      (e.homeomorph ((NativeLocalCoverPullback.toOriginal Y ωY π b T u hBranch i).symm y))) = _
  rw [he, NativeLocalCoverPullback.cover_map_value, Homeomorph.apply_symm_apply]

def reconstruction {i j : ι}
    (e : MNEC.NativeDifferentialEquiv.Equiv
      (fixedDifferential Y ωY π b T u hBranch i) (fixedDifferential Y ωY π b T u hBranch j))
    (he : ∀ z, (fixedCover Y ωY π b T u hBranch j).map (e.homeomorph z) =
      (fixedCover Y ωY π b T u hBranch i).map z) :
    MNEC.NativeDifferentialEquiv.Equiv (ωY i) (familyDifferential Y ωY π b T u hBranch j (u i)) :=
  NativeCoverIsomorphism.equivalence_of_commutes (π i) (familyCover Y ωY π b T u hBranch j (u i))
    (reconstructionHomeomorph Y ωY π b T u hBranch e)
    (reconstruction_square Y ωY π b T u hBranch e he)

theorem finite_local_exhaustion {d : ℕ}
    (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d) :
    ∃ J : Set ι, J.Finite ∧ ∀ i, ∃ j ∈ J,
      ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY i)
        (familyDifferential Y ωY π b T u hBranch j (u i)),
        ∀ y, (familyCover Y ωY π b T u hBranch j (u i)).map (e.homeomorph y) = (π i).map y := by
  let r := NativeCoverFamilyFiniteness.coverSetoid (FixedSource Y ωY π b T u hBranch)
    (fixedDifferential Y ωY π b T u hBranch) (fixedCover Y ωY π b T u hBranch)
  let : Finite (Quotient r) := NativeLocalCoverPullback.finite_classes Y ωY π b T u hBranch hdegree
  obtain ⟨J, hJ, hrep⟩ := FiniteClassRepresentatives.exists_representatives r
  refine ⟨J, hJ, ?_⟩
  intro i
  obtain ⟨j, hj, e, he⟩ := hrep i
  exact ⟨j, hj, reconstruction Y ωY π b T u hBranch e he,
    reconstruction_square Y ωY π b T u hBranch e he⟩

end VeechDichotomy.NativeLocalCoverExhaustion
