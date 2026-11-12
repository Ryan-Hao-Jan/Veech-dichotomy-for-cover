module

public import VeechDichotomy.NativePuncturedCover

/-! The actual positive sheet degree is constant on the FULL branch-value
complement, including zeros of the base differential. No degree or
local-triviality certificate is supplied as extra cover data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFullCoverDegree

open MNEC.NativeAbelianDifferential NativeTranslationCover NativePuncturedCover Set
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

def sheetNumber (π : Cover ωX ωY) (x : base π) : ℕ := Nat.card (π.map ⁻¹' {x.val})

theorem sheetNumber_locallyConstant (π : Cover ωX ωY) : IsLocallyConstant (sheetNumber π) :=
  isLocallyConstant_fiberCard_on_covering (isCoveringMapOn_base π)

theorem sheetNumber_constant (π : Cover ωX ωY) (x y : base π) : sheetNumber π x = sheetNumber π y := by
  let : PreconnectedSpace (base π) := isPreconnected_iff_preconnectedSpace.mp
    (base_pathConnected π).isConnected.isPreconnected
  exact (sheetNumber_locallyConstant π).apply_eq_of_preconnectedSpace x y

theorem sheetNumber_pos (π : Cover ωX ωY) (x : base π) : 0 < sheetNumber π x := by
  let : Finite (π.map ⁻¹' {x.val}) := (π.finite_fibers x.val).to_subtype
  obtain ⟨y, hy⟩ := π.surjective x.val
  let : Nonempty (π.map ⁻¹' {x.val}) := ⟨⟨y, hy⟩⟩
  exact Nat.card_pos

def reference (π : Cover ωX ωY) : base π :=
  ⟨Classical.choose (base_pathConnected π).nonempty, Classical.choose_spec (base_pathConnected π).nonempty⟩

def degree (π : Cover ωX ωY) : ℕ := sheetNumber π (reference π)

theorem degree_pos (π : Cover ωX ωY) : 0 < degree π := sheetNumber_pos π (reference π)

theorem fiber_card_eq_degree (π : Cover ωX ωY) {x : X} (hx : x ∉ branchValues π) :
    Nat.card (π.map ⁻¹' {x}) = degree π := sheetNumber_constant π ⟨x, hx⟩ (reference π)

end VeechDichotomy.NativeFullCoverDegree
