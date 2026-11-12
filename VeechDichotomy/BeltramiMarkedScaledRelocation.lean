module

public import VeechDichotomy.BeltramiMarkedScaledFamily
public import VeechDichotomy.BeltramiMarkedFiberZero

/-! Actual form-preserving identifications for the scalar-extended
native fibers. Deform and scale the original cover first, then relocate
its branches; the result is the constructed proper family's true fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedScaledRelocation

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
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

abbrev deformedCover := NativeDifferentialScale.cover p.1 (BeltramiMarkedFiberRelocation.deformedCover π p.2)

include hBranch in
theorem forward_near : ∀ x ∈ branchValues (deformedCover π p), ∀ᶠ z in 𝓝 x,
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFiberRelocation.transport F p.2) z :=
  BeltramiMarkedFiberRelocation.forward_near π F hBranch p.2

include hBranch in
theorem inverse_near : ∀ x ∈ branchValues (deformedCover π p),
    ∀ᶠ z in 𝓝 (BeltramiMarkedFiberRelocation.transport F p.2 x),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFiberRelocation.transport F p.2).symm z :=
  BeltramiMarkedFiberRelocation.inverse_near π F hBranch p.2

abbrev RelocatedSource := RelocatedCoverAtlas.Surface (deformedCover π p) (BeltramiMarkedFiberRelocation.transport F p.2)
  (forward_near π F hBranch p) (inverse_near π F hBranch p)

abbrev relocatedForm := RelocatedCoverDifferential.form (deformedCover π p) (BeltramiMarkedFiberRelocation.transport F p.2)
  (forward_near π F hBranch p) (inverse_near π F hBranch p)

abbrev relocatedCover := RelocatedCoverDifferential.cover (deformedCover π p) (BeltramiMarkedFiberRelocation.transport F p.2)
  (forward_near π F hBranch p) (inverse_near π F hBranch p)

def sourceHomeomorph : BeltramiMarkedFiberSurface.Surface π F hBranch p.2 ≃ₜ RelocatedSource π F hBranch p :=
  (BeltramiMarkedFiberMap.toBeltramiSource π F hBranch p.2).trans
    (RelocatedCoverAtlas.toOriginal (deformedCover π p) (BeltramiMarkedFiberRelocation.transport F p.2)
      (forward_near π F hBranch p) (inverse_near π F hBranch p)).symm

def equivalence : MNEC.NativeDifferentialEquiv.Equiv (fiberForm π F hBranch p) (relocatedForm π F hBranch p) :=
  NativeCoverIsomorphism.equivalence_of_commutes (cover π F hBranch p) (relocatedCover π F hBranch p)
    (sourceHomeomorph π F hBranch p) (by intro y; rfl)

def zeroEquivalence (hzero : ∀ i, p.2.val.2 i = 0) : MNEC.NativeDifferentialEquiv.Equiv
    (fiberForm π F hBranch p)
    (NativeDifferentialScale.form p.1 (NativeBeltramiDifferential.form qY (BeltramiMarkedReferenceCharts.parameter A p.2))) :=
  NativeDifferentialScale.equivalence p.1 (BeltramiMarkedFiberZero.equivalence π F hBranch p.2 hzero)

end VeechDichotomy.BeltramiMarkedScaledRelocation
