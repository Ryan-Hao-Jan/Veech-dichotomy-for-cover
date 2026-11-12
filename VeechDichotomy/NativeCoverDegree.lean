module

public import VeechDichotomy.NativeUnramifiedCover
public import Jacobians.MappingDegree.PathConnectedComplFinite
public import Mathlib.Topology.LocallyConstant.Basic

/-! The actual cover has a finite, constant sheet number off its branch
values and the base zeros. Local constancy is derived from ordinary
covering charts; constancy follows from connectedness of a finite-punctured
complex curve. No degree or local-triviality certificate is assumed.
-/

@[expose] public section
noncomputable section

open Set Filter Topology

namespace VeechDichotomy

theorem isLocallyConstant_fiberCard_on_covering
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
    {S : Set X} (hf : IsCoveringMapOn f S) :
    IsLocallyConstant (fun x : S => Nat.card (f ⁻¹' {x.val})) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨hd, U, hxU, hU, hfU, H, hH⟩ := hf x.val x.property
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU, ?_⟩
  intro y hy
  have hcoverY : IsEvenlyCovered f y.val (f ⁻¹' {x.val}) :=
    ⟨hd, U, hy, hU, hfU, H, hH⟩
  exact (Nat.card_congr hcoverY.fiberHomeomorph.toEquiv).symm

namespace NativeCoverDegree

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeUnramifiedCover
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

theorem unramifiedRegularBase_eq_compl_finite (π : Cover ωX ωY) :
    unramifiedRegularBase π = (zeroSet ωX ∪ branchValues π)ᶜ := by
  ext x
  simp only [unramifiedRegularBase, regularSet, Set.mem_sdiff, mem_compl_iff,
    mem_union, not_or]

theorem unramifiedRegularBase_pathConnected (π : Cover ωX ωY) :
    IsPathConnected (unramifiedRegularBase π) := by
  rw [unramifiedRegularBase_eq_compl_finite π]
  have hfin := (zeroSet_finite ωX).union (branchValues_finite π)
  let : Infinite X :=
    Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hne : ((zeroSet ωX ∪ branchValues π)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hfin.exists_notMem
    exact ⟨x, hx⟩
  exact Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
    hfin hne

def sheetNumber (π : Cover ωX ωY) (x : unramifiedRegularBase π) : ℕ :=
  Nat.card (π.map ⁻¹' {x.val})

theorem sheetNumber_locallyConstant (π : Cover ωX ωY) :
    IsLocallyConstant (sheetNumber π) :=
  isLocallyConstant_fiberCard_on_covering (isCoveringMapOn_unramifiedRegularBase π)

theorem sheetNumber_constant (π : Cover ωX ωY) (x y : unramifiedRegularBase π) :
    sheetNumber π x = sheetNumber π y := by
  let : PreconnectedSpace (unramifiedRegularBase π) :=
    isPreconnected_iff_preconnectedSpace.mp
      (unramifiedRegularBase_pathConnected π).isConnected.isPreconnected
  exact (sheetNumber_locallyConstant π).apply_eq_of_preconnectedSpace x y

theorem sheetNumber_pos (π : Cover ωX ωY) (x : unramifiedRegularBase π) :
    0 < sheetNumber π x := by
  let : Finite (π.map ⁻¹' {x.val}) := (π.finite_fibers x.val).to_subtype
  obtain ⟨y, hy⟩ := π.surjective x.val
  let : Nonempty (π.map ⁻¹' {x.val}) := ⟨⟨y, hy⟩⟩
  exact Nat.card_pos

/-- A positive finite degree is derived, rather than provided as a
separate geometric certificate in the cover data. -/
theorem exists_positive_degree (π : Cover ωX ωY) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : unramifiedRegularBase π, sheetNumber π x = d := by
  obtain ⟨x, hx⟩ := (unramifiedRegularBase_pathConnected π).nonempty
  let x₀ : unramifiedRegularBase π := ⟨x, hx⟩
  exact ⟨sheetNumber π x₀, sheetNumber_pos π x₀,
    fun y => sheetNumber_constant π y x₀⟩

end NativeCoverDegree
end VeechDichotomy
