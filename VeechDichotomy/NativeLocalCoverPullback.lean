module

public import VeechDichotomy.NativeLocalCoverFamily
public import VeechDichotomy.RelocatedCoverDegree
public import VeechDichotomy.NativeHurwitzFiberFiniteness

/-! Pull an arbitrary family of actual covers with nearby branch tuples
back to the fixed reference tuple. This is an explicit change of the source
complex structure, with unchanged actual degree, so monodromy finiteness
applies without an extra local triviality or degree certificate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverPullback

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Filter Topology
open NativeLocalCoverFamily
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

include hBranch

theorem forward_near (i : ι) : ∀ z ∈ branchValues (π i),
    ∀ᶠ x in 𝓝 z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (T.transport (u i)).symm x := by
  intro z hz
  rw [hBranch i] at hz
  obtain ⟨k, rfl⟩ := hz
  exact T.inverse_holomorphic_near (u i) k

theorem inverse_near (i : ι) : ∀ z ∈ branchValues (π i),
    ∀ᶠ x in 𝓝 ((T.transport (u i)).symm z),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (T.transport (u i)).symm.symm x := by
  intro z hz
  rw [hBranch i] at hz
  obtain ⟨k, rfl⟩ := hz
  rw [← T.moves (u i) k, Homeomorph.symm_apply_apply, Homeomorph.symm_symm]
  exact T.holomorphic_near (u i) k

abbrev Source (i : ι) := RelocatedCoverAtlas.Surface (π i) (T.transport (u i)).symm
  (forward_near Y ωY π b T u hBranch i) (inverse_near Y ωY π b T u hBranch i)

def toOriginal (i : ι) : Source Y ωY π b T u hBranch i ≃ₜ Y i :=
  RelocatedCoverAtlas.toOriginal (π i) (T.transport (u i)).symm
    (forward_near Y ωY π b T u hBranch i) (inverse_near Y ωY π b T u hBranch i)

def differential (i : ι) : Differential (Source Y ωY π b T u hBranch i) :=
  RelocatedCoverDifferential.form (π i) (T.transport (u i)).symm
    (forward_near Y ωY π b T u hBranch i) (inverse_near Y ωY π b T u hBranch i)

def cover (i : ι) : Cover ωX (differential Y ωY π b T u hBranch i) :=
  RelocatedCoverDifferential.cover (π i) (T.transport (u i)).symm
    (forward_near Y ωY π b T u hBranch i) (inverse_near Y ωY π b T u hBranch i)

@[simp] theorem cover_map_value (i : ι) (y : Y i) :
    (cover Y ωY π b T u hBranch i).map ((toOriginal Y ωY π b T u hBranch i).symm y) =
      (T.transport (u i)).symm ((π i).map y) := rfl

theorem branch_values (i : ι) : branchValues (cover Y ωY π b T u hBranch i) = range b := by
  rw [cover, RelocatedCoverBranchValues.branchValues_eq_image, hBranch i]
  ext x
  constructor
  · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    rw [← T.moves (u i) k, Homeomorph.symm_apply_apply]
  · rintro ⟨k, rfl⟩
    exact ⟨(u i).val k, ⟨k, rfl⟩, by rw [← T.moves (u i) k, Homeomorph.symm_apply_apply]⟩

theorem degree_eq (i : ι) : NativeFullCoverDegree.degree (cover Y ωY π b T u hBranch i) =
    NativeFullCoverDegree.degree (π i) :=
  RelocatedCoverDegree.degree_eq (π i) (T.transport (u i)).symm _ _

theorem finite_classes {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d) :
    Finite (Quotient (NativeCoverFamilyFiniteness.coverSetoid
      (Source Y ωY π b T u hBranch) (differential Y ωY π b T u hBranch)
      (cover Y ωY π b T u hBranch))) := by
  let : Infinite X := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := (finite_range b).exists_notMem
  apply NativeHurwitzFiberFiniteness.finite_classes
    (Source Y ωY π b T u hBranch) (differential Y ωY π b T u hBranch)
    (cover Y ωY π b T u hBranch) (finite_range b)
    (fun i => (branch_values Y ωY π b T u hBranch i).subset) ⟨x, hx⟩
  intro i
  calc
    Nat.card (NativeRelativePuncturedCover.map (cover Y ωY π b T u hBranch i) (range b) ⁻¹' {⟨x, hx⟩}) =
        Nat.card ((cover Y ωY π b T u hBranch i).map ⁻¹' {x}) :=
      Nat.card_congr (NativeRelativePuncturedCover.fiberEquiv _ _ _)
    _ = NativeFullCoverDegree.degree (cover Y ωY π b T u hBranch i) :=
      NativeFullCoverDegree.fiber_card_eq_degree _ (by
        rw [branch_values Y ωY π b T u hBranch i]
        exact hx)
    _ = NativeFullCoverDegree.degree (π i) := degree_eq Y ωY π b T u hBranch i
    _ = d := hdegree i

end VeechDichotomy.NativeLocalCoverPullback
