module

public import VeechDichotomy.BeltramiMarkedFiberBranchValues
public import VeechDichotomy.RelocatedCoverDifferential
public import VeechDichotomy.NativeCoverIsomorphism

/-! Each actual native fiber is genuinely form-preservingly equivalent
to deforming the original cover first and relocating its branches second.
The underlying homeomorphism is explicit; holomorphicity and form
preservation follow from the proved commuting-cover isomorphism theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberRelocation

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (a : ComplexBeltramiMarkParameters.Parameters A)

abbrev deformedCover := NativeBeltramiCover.cover π (BeltramiMarkedReferenceCharts.parameter A a)

def transport : NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a) ≃ₜ
    NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a) :=
  F.nativeMap (ComplexBeltramiMarkParameters.productHomeomorph A a)

include hBranch in
theorem forward_near : ∀ x ∈ branchValues (deformedCover π a),
    ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport F a) z := by
  intro x hx
  rw [NativeBeltramiCoverBranchValues.branch_tuple π (BeltramiMarkedReferenceCharts.parameter A a) b hBranch] at hx
  obtain ⟨i, rfl⟩ := hx
  exact F.holomorphic_near (ComplexBeltramiMarkParameters.productHomeomorph A a) i

include hBranch in
theorem inverse_near : ∀ x ∈ branchValues (deformedCover π a),
    ∀ᶠ z in 𝓝 (transport F a x), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport F a).symm z := by
  intro x hx
  rw [NativeBeltramiCoverBranchValues.branch_tuple π (BeltramiMarkedReferenceCharts.parameter A a) b hBranch] at hx
  obtain ⟨i, rfl⟩ := hx
  have h := F.inverse_holomorphic_near (ComplexBeltramiMarkParameters.productHomeomorph A a) i
  rw [← F.moves (ComplexBeltramiMarkParameters.productHomeomorph A a) i] at h
  exact h

abbrev RelocatedSource := RelocatedCoverAtlas.Surface (deformedCover π a) (transport F a)
  (forward_near π F hBranch a) (inverse_near π F hBranch a)

abbrev relocatedForm := RelocatedCoverDifferential.form (deformedCover π a) (transport F a)
  (forward_near π F hBranch a) (inverse_near π F hBranch a)

abbrev relocatedCover := RelocatedCoverDifferential.cover (deformedCover π a) (transport F a)
  (forward_near π F hBranch a) (inverse_near π F hBranch a)

def sourceHomeomorph : BeltramiMarkedFiberSurface.Surface π F hBranch a ≃ₜ RelocatedSource π F hBranch a :=
  (BeltramiMarkedFiberMap.toBeltramiSource π F hBranch a).trans
    (RelocatedCoverAtlas.toOriginal (deformedCover π a) (transport F a)
      (forward_near π F hBranch a) (inverse_near π F hBranch a)).symm

def equivalence : MNEC.NativeDifferentialEquiv.Equiv
    (BeltramiMarkedFiberDifferential.form π F hBranch a) (relocatedForm π F hBranch a) :=
  NativeCoverIsomorphism.equivalence_of_commutes (BeltramiMarkedFiberDifferential.cover π F hBranch a)
    (relocatedCover π F hBranch a) (sourceHomeomorph π F hBranch a) (by intro y; rfl)

theorem commutes (y : BeltramiMarkedFiberSurface.Surface π F hBranch a) :
    (relocatedCover π F hBranch a).map ((equivalence π F hBranch a).homeomorph y) =
      (BeltramiMarkedFiberDifferential.cover π F hBranch a).map y := rfl

end VeechDichotomy.BeltramiMarkedFiberRelocation
