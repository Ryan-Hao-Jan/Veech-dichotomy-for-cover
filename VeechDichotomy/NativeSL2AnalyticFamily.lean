module

public import VeechDichotomy.SL2BeltramiEquivalence
public import VeechDichotomy.NativeScaledBeltramiSubmersion
public import VeechDichotomy.HolomorphicCotangentForms
public import VeechDichotomy.HolomorphicCurveMaps
public import Mathlib.Topology.Sequences

/-! Actual native SL2 deformations of a fixed differential occur in one
constructed proper analytic family with continuously varying parameters.
The source identifications are genuine native differential equivalences,
and embeddings into the total space are holomorphic. Compact SL2 sets
therefore have actual analytic-family subsequence limits. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2AnalyticFamily

open MNEC.NativeAbelianDifferential LinearGroup SL2BeltramiParameters NativeScaledBeltramiFamily
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def parameters (A : SL2) : Base := (⟨scalar A, scalar_ne_zero A⟩, parameter A)

theorem continuous_parameters : Continuous parameters :=
  (continuous_scalar.subtype_mk _).prodMk continuous_parameter

theorem compact_parameters {K : Set SL2} (hK : IsCompact K) : IsCompact (parameters '' K) :=
  hK.image continuous_parameters

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

def equivalence (A : SL2) : MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form q A)
    (fiberForm q (parameters A)) := SL2BeltramiEquivalence.equivalence q A

def fiberHomeomorph (A : SL2) : WholeDeformedAtlas.WholeSurface q A ≃ₜ (projection q ⁻¹' {parameters A}) :=
  (equivalence q A).homeomorph.trans (NativeScaledBeltramiFamily.fiberHomeomorph q (parameters A))

def embedding (A : SL2) : WholeDeformedAtlas.WholeSurface q A → Total q :=
  inclusion q (parameters A) ∘ (equivalence q A).homeomorph

theorem projection_embedding (A : SL2) (x : WholeDeformedAtlas.WholeSurface q A) :
    projection q (embedding q A x) = parameters A := rfl

theorem holomorphic_embedding (A : SL2) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) ω (embedding q A) :=
  (holomorphic_inclusion q (parameters A)).comp
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable (equivalence q A).homeomorph (equivalence q A).differentiable)

theorem differential_pullback (A : SL2) :
    HolomorphicCotangentForms.pullback (equivalence q A).homeomorph
      (HolomorphicCurveMaps.contMDiff_of_mdifferentiable (equivalence q A).homeomorph (equivalence q A).differentiable)
      (fiberForm q (parameters A)).val = (WholeDeformedDifferential.form q A).val := by
  apply ContMDiffSection.ext
  intro x
  exact ((equivalence q A).oneForm_pullback x).symm

theorem compact_subsequence (a : ℕ → SL2) {K : Set SL2} (hK : IsCompact K) (ha : ∀ n, a n ∈ K) :
    ∃ A ∈ K, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => parameters (a (σ n))) atTop (𝓝 (parameters A)) ∧
      ∀ n, Nonempty (MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form q (a (σ n)))
        (fiberForm q (parameters (a (σ n))))) := by
  obtain ⟨p, hp, σ, hσ, hconv⟩ := (compact_parameters hK).tendsto_subseq (fun n => mem_image_of_mem parameters (ha n))
  obtain ⟨A, hA, rfl⟩ := hp
  exact ⟨A, hA, σ, hσ, hconv, fun n => ⟨equivalence q (a (σ n))⟩⟩

end VeechDichotomy.NativeSL2AnalyticFamily
