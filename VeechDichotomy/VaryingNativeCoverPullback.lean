module

public import VeechDichotomy.UniformSL2ConfigurationParameters
public import VeechDichotomy.NativeCoverUndeformation
public import VeechDichotomy.RelocatedCoverDegree

/-! Actual normalization of a native cover with a varying SL2 base and
nearby branches: identify the base with c*eta_mu, inverse-move its branches,
identify with the given SL2 base again, then apply the GIVEN inverse matrix.
The result is a genuine native cover of the fixed original pointed base. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingNativeCoverPullback

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (A : Data q b μ₀) (F : Family A) (L : SL2) (u : Fin m → X)
  (h : Valid A (SL2BeltramiParameters.parameter L) u)

local instance : ChartedSpace ℂ (WholeSurface q L) := WholeDeformedAtlas.chartedSpace q L
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q L) := WholeDeformedAtlas.isComplexManifold q L ω

variable (ρ : Cover (transformed q L) r)
  (hbranch : branchValues ρ = range (fun i => (toOriginal q L).symm (u i)))

abbrev nativeCover := NativeCoverEquivalence.postcompose ρ (baseEquivalence A L u h)

include hbranch in
theorem native_branch : branchValues (nativeCover A L u h ρ) =
    range (fun i => (⟨u i⟩ : NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L))) := by
  rw [nativeCover, NativeCoverEquivalence.branchValues_postcompose, hbranch, ← range_comp]
  rfl

include hbranch in
theorem inverse_forward_near : ∀ x ∈ branchValues (nativeCover A L u h ρ),
    ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport A F L u h).symm z := by
  intro x hx
  rw [native_branch A L u h ρ hbranch] at hx
  obtain ⟨i, rfl⟩ := hx
  let p := ComplexBeltramiMarkParameters.productHomeomorph A (markParameters A L u h)
  have hi := F.inverse_holomorphic_near p i
  have hc : (F.disks p.1 i).chart.symm (p.2 i).val =
      (⟨u i⟩ : NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L)) :=
    (F.moves p i).symm.trans (transport_moves A F L u h i)
  rw [hc] at hi
  exact hi

include hbranch in
theorem inverse_inverse_near : ∀ x ∈ branchValues (nativeCover A L u h ρ),
    ∀ᶠ z in 𝓝 ((transport A F L u h).symm x),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport A F L u h).symm.symm z := by
  intro x hx
  rw [native_branch A L u h ρ hbranch] at hx
  obtain ⟨i, rfl⟩ := hx
  change ∀ᶠ z in 𝓝 ((transport A F L u h).symm ⟨u i⟩),
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport A F L u h).symm.symm z
  rw [← transport_moves A F L u h i, Homeomorph.symm_apply_apply, Homeomorph.symm_symm]
  exact F.holomorphic_near (ComplexBeltramiMarkParameters.productHomeomorph A (markParameters A L u h)) i

abbrev FixedSource := RelocatedCoverAtlas.Surface (nativeCover A L u h ρ) (transport A F L u h).symm
  (inverse_forward_near A F L u h ρ hbranch) (inverse_inverse_near A F L u h ρ hbranch)

def fixedDifferential : Differential (FixedSource A F L u h ρ hbranch) :=
  RelocatedCoverDifferential.form (nativeCover A L u h ρ) (transport A F L u h).symm
    (inverse_forward_near A F L u h ρ hbranch) (inverse_inverse_near A F L u h ρ hbranch)

def fixedNativeCover : Cover (BeltramiMarkedScaledFamily.baseFiberForm (familyParameters A L u h))
    (fixedDifferential A F L u h ρ hbranch) :=
  RelocatedCoverDifferential.cover (nativeCover A L u h ρ) (transport A F L u h).symm
    (inverse_forward_near A F L u h ρ hbranch) (inverse_inverse_near A F L u h ρ hbranch)

def fixedWholeCover : Cover (transformed q L) (fixedDifferential A F L u h ρ hbranch) :=
  NativeCoverEquivalence.postcompose (fixedNativeCover A F L u h ρ hbranch)
    (NativeDifferentialEquivalenceLaws.symm (baseEquivalence A L u h))

theorem fixed_native_branch : branchValues (fixedNativeCover A F L u h ρ hbranch) =
    range (fun i => (⟨b i⟩ : NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L))) := by
  rw [fixedNativeCover, RelocatedCoverBranchValues.branchValues_eq_image, native_branch A L u h ρ hbranch, ← range_comp]
  apply congrArg Set.range
  funext i
  change (transport A F L u h).symm (⟨u i⟩ : NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L)) = ⟨b i⟩
  rw [← transport_moves A F L u h i, Homeomorph.symm_apply_apply]

theorem fixed_whole_branch : branchValues (fixedWholeCover A F L u h ρ hbranch) =
    range (fun i => (toOriginal q L).symm (b i)) := by
  rw [fixedWholeCover, NativeCoverEquivalence.branchValues_postcompose, fixed_native_branch, ← range_comp]
  rfl

def NormalizedSource := WholeSurface (fixedDifferential A F L u h ρ hbranch) L⁻¹

instance normalizedTopology : TopologicalSpace (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.topology (fixedDifferential A F L u h ρ hbranch) L⁻¹
instance normalizedT2Space : T2Space (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.t2Space (fixedDifferential A F L u h ρ hbranch) L⁻¹
instance normalizedCompactSpace : CompactSpace (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.compactSpace (fixedDifferential A F L u h ρ hbranch) L⁻¹
instance normalizedConnectedSpace : ConnectedSpace (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.connectedSpace (fixedDifferential A F L u h ρ hbranch) L⁻¹
instance normalizedChartedSpace : ChartedSpace ℂ (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.chartedSpace (fixedDifferential A F L u h ρ hbranch) L⁻¹
instance normalizedIsManifold : IsManifold 𝓘(ℂ) ω (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedAtlas.isComplexManifold (fixedDifferential A F L u h ρ hbranch) L⁻¹ ω

def normalizedDifferential : Differential (NormalizedSource A F L u h ρ hbranch) :=
  WholeDeformedDifferential.form (fixedDifferential A F L u h ρ hbranch) L⁻¹

def normalizedCover : Cover q (normalizedDifferential A F L u h ρ hbranch) :=
  NativeCoverUndeformation.cover q L (fixedWholeCover A F L u h ρ hbranch)

def fromOriginal : Y ≃ₜ NormalizedSource A F L u h ρ hbranch :=
  (RelocatedCoverAtlas.toOriginal (nativeCover A L u h ρ) (transport A F L u h).symm
    (inverse_forward_near A F L u h ρ hbranch) (inverse_inverse_near A F L u h ρ hbranch)).symm.trans
      (toOriginal (fixedDifferential A F L u h ρ hbranch) L⁻¹).symm

theorem normalized_map_value (y : Y) :
    (normalizedCover A F L u h ρ hbranch).map (fromOriginal A F L u h ρ hbranch y) =
      (BeltramiMarkedBaseTransport.transported F (markParameters A L u h)).symm (ρ.map y).point := rfl

theorem normalized_branch : branchValues (normalizedCover A F L u h ρ hbranch) = range b := by
  rw [normalizedCover, NativeCoverUndeformation.branch_values, fixed_whole_branch, ← range_comp]
  rfl

theorem normalized_degree : NativeFullCoverDegree.degree (normalizedCover A F L u h ρ hbranch) =
    NativeFullCoverDegree.degree ρ := by
  calc
    NativeFullCoverDegree.degree (normalizedCover A F L u h ρ hbranch) =
        NativeFullCoverDegree.degree (fixedWholeCover A F L u h ρ hbranch) := NativeCoverUndeformation.degree_eq _ _ _
    _ = NativeFullCoverDegree.degree (fixedNativeCover A F L u h ρ hbranch) := NativeCoverDegreeTransport.degree_postcompose _ _
    _ = NativeFullCoverDegree.degree (nativeCover A L u h ρ) := RelocatedCoverDegree.degree_eq _ _ _ _
    _ = NativeFullCoverDegree.degree ρ := NativeCoverDegreeTransport.degree_postcompose _ _

end VeechDichotomy.VaryingNativeCoverPullback
