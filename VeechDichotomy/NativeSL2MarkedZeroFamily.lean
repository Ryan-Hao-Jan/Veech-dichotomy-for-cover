module

public import VeechDichotomy.BeltramiMarkedScaledEmbeddings
public import VeechDichotomy.NativeSL2AnalyticFamily

/-! Actual native SL2 deformations of the fixed reference covering
source occur in the constructed simultaneous family's zero-displacement
fibers, with genuine differential equivalences and holomorphic embeddings. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2MarkedZeroFamily

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology LinearGroup
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π) (p : Base A)

local instance (L : SL2) : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface qY L) := WholeDeformedAtlas.chartedSpace qY L
local instance (L : SL2) : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface qY L) := WholeDeformedAtlas.isComplexManifold qY L ω

def equivalence (L : SL2)
    (hp : (p.1, BeltramiMarkedReferenceCharts.parameter A p.2) = NativeSL2AnalyticFamily.parameters L)
    (hzero : ∀ i, p.2.val.2 i = 0) :
    MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form qY L) (fiberForm π F hBranch p) := by
  have he : MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form qY L)
      (NativeDifferentialScale.form p.1 (NativeBeltramiDifferential.form qY (BeltramiMarkedReferenceCharts.parameter A p.2))) := by
    have h := NativeSL2AnalyticFamily.equivalence qY L
    rw [← hp] at h
    exact h
  exact NativeDifferentialEquivalenceLaws.trans he
    (NativeDifferentialEquivalenceLaws.symm (BeltramiMarkedScaledRelocation.zeroEquivalence π F hBranch p hzero))

def embedding (L : SL2)
    (hp : (p.1, BeltramiMarkedReferenceCharts.parameter A p.2) = NativeSL2AnalyticFamily.parameters L)
    (hzero : ∀ i, p.2.val.2 i = 0) : WholeDeformedAtlas.WholeSurface qY L → Total π F hBranch :=
  BeltramiMarkedScaledEmbeddings.embedding π F hBranch p (equivalence π F hBranch p L hp hzero)

theorem holomorphic_embedding (L : SL2)
    (hp : (p.1, BeltramiMarkedReferenceCharts.parameter A p.2) = NativeSL2AnalyticFamily.parameters L)
    (hzero : ∀ i, p.2.val.2 i = 0) : ContMDiff 𝓘(ℂ)
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) ω (embedding π F hBranch p L hp hzero) :=
  BeltramiMarkedScaledEmbeddings.holomorphic_embedding π F hBranch p (equivalence π F hBranch p L hp hzero)

theorem projection_embedding (L : SL2)
    (hp : (p.1, BeltramiMarkedReferenceCharts.parameter A p.2) = NativeSL2AnalyticFamily.parameters L)
    (hzero : ∀ i, p.2.val.2 i = 0) (y : WholeDeformedAtlas.WholeSurface qY L) :
    projection π F hBranch (embedding π F hBranch p L hp hzero y) = p := rfl

end VeechDichotomy.NativeSL2MarkedZeroFamily
