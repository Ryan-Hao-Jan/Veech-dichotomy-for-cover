module

public import VeechDichotomy.BeltramiMarkedScaledRelocation

/-! Actual native differential equivalences embed arbitrary source
curves holomorphically onto the scalar-extended family's true fibers,
preserving the intrinsic native covering differential. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedScaledEmbeddings

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {qZ : Differential Z} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (p : Base A) (e : MNEC.NativeDifferentialEquiv.Equiv qZ (fiberForm π F hBranch p))

def fiberHomeomorph : Z ≃ₜ (projection π F hBranch ⁻¹' {p}) :=
  e.homeomorph.trans (BeltramiMarkedScaledFamily.fiberHomeomorph π F hBranch p)

def embedding : Z → Total π F hBranch := inclusion π F hBranch p ∘ e.homeomorph

theorem projection_embedding (z : Z) : projection π F hBranch (embedding π F hBranch p e z) = p := rfl

theorem holomorphic_embedding : ContMDiff 𝓘(ℂ)
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) ω (embedding π F hBranch p e) :=
  (holomorphic_inclusion π F hBranch p).comp
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)

theorem differential_pullback : Jacobians.pullbackForm e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (fiberForm π F hBranch p).val = qZ.val := by
  apply ContMDiffSection.ext
  intro z
  exact (e.oneForm_pullback z).symm

theorem covering_pullback :
    Jacobians.pullbackForm ((cover π F hBranch p).map ∘ e.homeomorph)
      ((cover π F hBranch p).holomorphic.comp
        (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable))
      (baseFiberForm p).val = qZ.val := by
  rw [Jacobians.pullbackForm_comp e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (cover π F hBranch p).map (cover π F hBranch p).holomorphic]
  change Jacobians.pullbackForm e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (Jacobians.pullbackForm (cover π F hBranch p).map (cover π F hBranch p).holomorphic (baseFiberForm p).val) = qZ.val
  rw [(cover π F hBranch p).pullback_eq]
  exact differential_pullback π F hBranch p e

end VeechDichotomy.BeltramiMarkedScaledEmbeddings
