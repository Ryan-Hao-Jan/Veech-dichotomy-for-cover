module

public import VeechDichotomy.RelocatedCoverBranchValues

/-! Genuine local families of native finite translation covers with
moving ordered branch values. The transport data is constructed by the
proved local configuration theorem; source complex structures, nonzero
forms and native holomorphic covers are computed from it. Only continuity
of the underlying maps is asserted here, not ambient moduli continuity.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverFamily

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

section TransportData

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {m : ℕ}

structure MarkTransport (b : Fin m → X) where
  neighborhood : Set (Fin m → X)
  open_neighborhood : IsOpen neighborhood
  contains : b ∈ neighborhood
  distinct : neighborhood ⊆ configuration m X
  transport : neighborhood → X ≃ₜ X
  continuous_transport : Continuous (fun p : neighborhood × X => transport p.1 p.2)
  continuous_inverse : Continuous (fun p : neighborhood × X => (transport p.1).symm p.2)
  identity : ∀ u : neighborhood, u.val = b → transport u = Homeomorph.refl X
  moves : ∀ u : neighborhood, ∀ i, transport u (b i) = u.val i
  holomorphic_near : ∀ u : neighborhood, ∀ i,
    ∀ᶠ x in 𝓝 (b i), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport u) x
  inverse_holomorphic_near : ∀ u : neighborhood, ∀ i,
    ∀ᶠ x in 𝓝 (u.val i), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (transport u).symm x
  isotopy : ∀ u : neighborhood, ∃ J : unitInterval → X ≃ₜ X,
    J 0 = Homeomorph.refl X ∧ J 1 = transport u ∧
    Continuous (fun p : unitInterval × X => J p.1 p.2) ∧
    Continuous (fun p : unitInterval × X => (J p.1).symm p.2)

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem nonempty_transport (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) :
    Nonempty (MarkTransport b) := by
  obtain ⟨Ω, hΩ, hbΩ, hconf, ψ, hψ, hInv, hid, hmove, hHol, hInvHol, hIso⟩ :=
    NativeConfigurationTransport.exists_local_transport q b hb
  exact ⟨⟨Ω, hΩ, hbΩ, hconf, ψ, hψ, hInv, hid, hmove, hHol, hInvHol, hIso⟩⟩

def chosenTransport (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) : MarkTransport b :=
  Classical.choice (nonempty_transport q b hb)

end TransportData

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) (b : Fin m → X) (hBranch : range b = branchValues π) (T : MarkTransport b)

include hBranch

theorem forward_near_branch (u : T.neighborhood) :
    ∀ z ∈ branchValues π, ∀ᶠ x in 𝓝 z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (T.transport u) x := by
  intro z hz
  have hzRange : z ∈ range b := by rw [hBranch]; exact hz
  obtain ⟨i, hi⟩ := hzRange
  rw [← hi]
  exact T.holomorphic_near u i

theorem inverse_near_branch (u : T.neighborhood) :
    ∀ z ∈ branchValues π, ∀ᶠ x in 𝓝 (T.transport u z), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (T.transport u).symm x := by
  intro z hz
  have hzRange : z ∈ range b := by rw [hBranch]; exact hz
  obtain ⟨i, hi⟩ := hzRange
  rw [← hi, T.moves u i]
  exact T.inverse_holomorphic_near u i

abbrev Source (u : T.neighborhood) :=
  RelocatedCoverAtlas.Surface π (T.transport u) (forward_near_branch π b hBranch T u)
    (inverse_near_branch π b hBranch T u)

def toOriginal (u : T.neighborhood) : Source π b hBranch T u ≃ₜ Y :=
  RelocatedCoverAtlas.toOriginal π (T.transport u) (forward_near_branch π b hBranch T u)
    (inverse_near_branch π b hBranch T u)

def differential (u : T.neighborhood) : Differential (Source π b hBranch T u) :=
  RelocatedCoverDifferential.form π (T.transport u) (forward_near_branch π b hBranch T u)
    (inverse_near_branch π b hBranch T u)

def cover (u : T.neighborhood) : Cover ωX (differential π b hBranch T u) :=
  RelocatedCoverDifferential.cover π (T.transport u) (forward_near_branch π b hBranch T u)
    (inverse_near_branch π b hBranch T u)

@[simp] theorem cover_map_value (u : T.neighborhood) (y : Y) :
    (cover π b hBranch T u).map ((toOriginal π b hBranch T u).symm y) = T.transport u (π.map y) := rfl

theorem branch_values (u : T.neighborhood) : branchValues (cover π b hBranch T u) = range u.val := by
  have h := RelocatedCoverBranchValues.branch_tuple π (T.transport u)
    (forward_near_branch π b hBranch T u) (inverse_near_branch π b hBranch T u) b hBranch
  have heq : (fun i => T.transport u (b i)) = u.val := funext (T.moves u)
  rw [heq] at h
  exact h.symm

theorem continuous_underlying_family :
    Continuous (fun p : T.neighborhood × Y =>
      (cover π b hBranch T p.1).map ((toOriginal π b hBranch T p.1).symm p.2)) :=
  NativeMovingCoverMap.continuous_family π T.transport T.continuous_transport

def original_equivalence (u : T.neighborhood) (hu : u.val = b) :
    MNEC.NativeDifferentialEquiv.Equiv (differential π b hBranch T u) ωY :=
  RelocatedCoverBranchValues.equivalence_at_identity π (T.transport u)
    (forward_near_branch π b hBranch T u) (inverse_near_branch π b hBranch T u) (T.identity u hu)

end VeechDichotomy.NativeLocalCoverFamily
