module

public import VeechDichotomy.BeltramiMarkedFiberRelocation
public import VeechDichotomy.HolomorphicCurveMaps

/-! Actual native differential equivalences give holomorphic embeddings
onto the constructed simultaneous family's fibers. The native fiber form
and its actual covering pullback preserve the original differential. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberEmbeddings

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
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
  (a : ComplexBeltramiMarkParameters.Parameters A)
  (e : MNEC.NativeDifferentialEquiv.Equiv qZ (BeltramiMarkedFiberDifferential.form π F hBranch a))

def fiberHomeomorph : Z ≃ₜ (BeltramiMarkedCoverTotalSpace.projection π F hBranch ⁻¹' {a}) :=
  e.homeomorph.trans (BeltramiMarkedFiberSurface.fiberHomeomorph π F hBranch a)

def embedding : Z → BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch :=
  BeltramiMarkedFiberSurface.inclusion π F hBranch a ∘ e.homeomorph

theorem projection_embedding (z : Z) :
    BeltramiMarkedCoverTotalSpace.projection π F hBranch (embedding π F hBranch a e z) = a := rfl

theorem holomorphic_embedding : ContMDiff 𝓘(ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (embedding π F hBranch a e) :=
  (BeltramiMarkedFiberSurface.holomorphic_inclusion π F hBranch a).comp
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)

theorem differential_pullback : Jacobians.pullbackForm e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (BeltramiMarkedFiberDifferential.form π F hBranch a).val = qZ.val := by
  apply ContMDiffSection.ext
  intro z
  exact (e.oneForm_pullback z).symm

theorem covering_pullback :
    Jacobians.pullbackForm ((BeltramiMarkedFiberDifferential.cover π F hBranch a).map ∘ e.homeomorph)
      ((BeltramiMarkedFiberDifferential.cover π F hBranch a).holomorphic.comp
        (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable))
      (NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A a)).val = qZ.val := by
  rw [Jacobians.pullbackForm_comp e.homeomorph
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (BeltramiMarkedFiberDifferential.cover π F hBranch a).map
    (BeltramiMarkedFiberDifferential.cover π F hBranch a).holomorphic]
  exact differential_pullback π F hBranch a e

end VeechDichotomy.BeltramiMarkedFiberEmbeddings
