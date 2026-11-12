module

public import VeechDichotomy.NativeAnalyticCoverForm

/-! Actual native differential equivalences give holomorphic embeddings
onto the analytic family's fibers. The total holomorphic form pulls back
to the ORIGINAL native differential, not just an isomorphic coefficient
model. This transfers the analytic families to arbitrary native covers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverEmbeddings

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open NativeAnalyticCoverTotalSpace ComplexDisplacementParameters HolomorphicCotangentForms
open Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {ωX : Differential X} {ωY : Differential Y} {ωZ : Differential Z} {m : ℕ}
variable (π : Cover ωX ωY) (b : Fin m → X) (hBranch : range b = branchValues π) (A : Data b)
  (a : Parameters m)
  (e : MNEC.NativeDifferentialEquiv.Equiv ωZ (NativeLocalCoverFamily.differential π b hBranch A.marks (A.tuple a)))

def fiberHomeomorph : Z ≃ₜ (projection π A hBranch ⁻¹' {a}) :=
  e.homeomorph.trans (NativeAnalyticCoverFiberCharts.fiberHomeomorph π b hBranch A a)

def embedding : Z → TotalSpace π A hBranch :=
  NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a ∘ e.homeomorph

theorem projection_embedding (z : Z) : projection π A hBranch (embedding π b hBranch A a e z) = a := rfl

theorem holomorphic_embedding : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Space m × ℂ) ω (embedding π b hBranch A a e) :=
  (NativeAnalyticCoverFiberCharts.holomorphic_inclusion π b hBranch A a).comp
    (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)

theorem differential_pullback :
    pullback (embedding π b hBranch A a e) (holomorphic_embedding π b hBranch A a e)
      (NativeAnalyticCoverForm.form π A hBranch) = ωZ.val := by
  change pullback (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a ∘ e.homeomorph) _ _ = _
  rw [← pullback_comp e.homeomorph (HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable)
    (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a)
    (NativeAnalyticCoverFiberCharts.holomorphic_inclusion π b hBranch A a), NativeAnalyticCoverForm.fiber_pullback_eq]
  apply ContMDiffSection.ext
  intro z
  exact (e.oneForm_pullback z).symm

theorem covering_square (ρ : Cover ωX ωZ)
    (he : ∀ z, (NativeLocalCoverFamily.cover π b hBranch A.marks (A.tuple a)).map (e.homeomorph z) = ρ.map z)
    (z : Z) : NativeAnalyticCoverProjection.map π A hBranch (embedding π b hBranch A a e z) = ρ.map z :=
  (NativeAnalyticCoverProjection.fiber_cover_map π A hBranch a (e.homeomorph z)).symm.trans (he z)

end VeechDichotomy.NativeAnalyticCoverEmbeddings
