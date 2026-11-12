module

public import VeechDichotomy.NativeCoverFamilyLimits
public import VeechDichotomy.NativeCompactNormalizedCovers

/-! Concrete sequences of normalized native covers. The corrected
base matrix is A_n*gamma_n; the source is still the ACTUAL native
deformation by A_n. Actual degree, branches and family limits follow
without an affine lift to the covering source. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeNormalizedCoverSequences

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup NativeVeech
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def matrix (a γ : ℕ → SL2) (n : ℕ) : SL2 := a n * γ n

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y}

def branches {m : ℕ} (b : Fin m → X) {γ : ℕ → SL2} (φ : ∀ n, AffineAutomorphism qX (γ n)) (n : ℕ) : Fin m → X :=
  fun i => (φ n).surface.symm (b i)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qX B) := WholeDeformedAtlas.chartedSpace qX B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qX B) := WholeDeformedAtlas.isComplexManifold qX B ω
local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qY B) := WholeDeformedAtlas.chartedSpace qY B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qY B) := WholeDeformedAtlas.isComplexManifold qY B ω

variable (π : Cover qX qY) (a γ : ℕ → SL2) (φ : ∀ n, AffineAutomorphism qX (γ n))

def cover (n : ℕ) : Cover (transformed qX (matrix a γ n)) (transformed qY (a n)) :=
  NativeNormalizedCover.normalizedCover π (φ n) (a n)

theorem branch_tuple {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π) (n : ℕ) :
    branchValues (cover π a γ φ n) = range (fun i => (toOriginal qX (matrix a γ n)).symm (branches b φ n i)) :=
  (NativeNormalizedCover.normalized_branch_tuple π (φ n) (a n) b hb).symm

theorem degree_eq (n : ℕ) : NativeFullCoverDegree.degree (cover π a γ φ n) = NativeFullCoverDegree.degree π :=
  (NativeCoverDegreeTransport.degree_postcompose _ _).trans (NativeCoverDegreeTransport.degree_deformation π (a n))

theorem compact_family_limit {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π)
    {K : Set SL2} (hK : IsCompact K) (hmat : ∀ n, matrix a γ n ∈ K)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hmarks : ∀ n, branches b φ n ∈ C) (hconf : C ⊆ configuration m X) :
    NativeCoverFamilyLimits.FamilyLimit (fun n => WholeSurface qY (a n)) (matrix a γ) (branches b φ)
      (fun n => transformed qY (a n)) (cover π a γ φ) (branch_tuple π a γ φ b hb) K C :=
  NativeCoverFamilyLimits.family_limit (fun n => WholeSurface qY (a n)) (matrix a γ) (branches b φ)
    (fun n => transformed qY (a n)) (cover π a γ φ) (branch_tuple π a γ φ b hb)
    (degree_eq π a γ φ) hK hmat hC hmarks hconf

end VeechDichotomy.NativeNormalizedCoverSequences
