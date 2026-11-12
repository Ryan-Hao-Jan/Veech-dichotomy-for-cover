module

public import VeechDichotomy.NativePuncturedCover
public import VeechDichotomy.CoverMonodromy

/-! The actual finite permutation representation of the punctured base's
fundamental group supplied by a genuine connected translation cover.
Transitivity is derived from path connectedness of the punctured source. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverMonodromy

open MNEC.NativeAbelianDifferential NativeTranslationCover NativePuncturedCover Set Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

abbrev Fiber (π : Cover ωX ωY) (x : base π) := puncturedMap π ⁻¹' {x}

def representation (π : Cover ωX ωY) (x : base π) :
    FundamentalGroup (base π) x →* Equiv.Perm (Fiber π x) :=
  (isCoveringMap_puncturedMap π).monodromyPerm x

theorem representation_transitive (π : Cover ωX ωY) (x : base π) (a b : Fiber π x) :
    ∃ γ : FundamentalGroup (base π) x, representation π x γ a = b := by
  let : PathConnectedSpace (source π) := isPathConnected_iff_pathConnectedSpace.mp (source_pathConnected π)
  exact CoverMonodromy.transitive (isCoveringMap_puncturedMap π) x a b

theorem fiber_card_pos (π : Cover ωX ωY) (x : base π) : 0 < Nat.card (Fiber π x) := by
  let : Finite (Fiber π x) := fiber_finite π x
  obtain ⟨y, hy⟩ := puncturedMap_surjective π x
  let : Nonempty (Fiber π x) := ⟨⟨y, hy⟩⟩
  exact Nat.card_pos

def labelFiber (π : Cover ωX ωY) (x : base π) : Fiber π x ≃ Fin (Nat.card (Fiber π x)) := by
  let : Finite (Fiber π x) := fiber_finite π x
  exact Finite.equivFin _

def numberedRepresentation (π : Cover ωX ωY) (x : base π) :
    FundamentalGroup (base π) x →* Equiv.Perm (Fin (Nat.card (Fiber π x))) :=
  (labelFiber π x).permCongrHom.toMonoidHom.comp (representation π x)

theorem numberedRepresentation_transitive (π : Cover ωX ωY) (x : base π)
    (i j : Fin (Nat.card (Fiber π x))) :
    ∃ γ : FundamentalGroup (base π) x, numberedRepresentation π x γ i = j := by
  obtain ⟨γ, hγ⟩ := representation_transitive π x ((labelFiber π x).symm i) ((labelFiber π x).symm j)
  refine ⟨γ, ?_⟩
  change labelFiber π x (representation π x γ ((labelFiber π x).symm i)) = j
  rw [hγ, Equiv.apply_symm_apply]

end VeechDichotomy.NativeCoverMonodromy
