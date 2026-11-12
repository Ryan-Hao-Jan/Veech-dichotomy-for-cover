module

public import VeechDichotomy.NativeAffinePowers
public import VeechDichotomy.FiniteFiberPeriodicity

/-! Actual native affine automorphisms permute the genuine finite zero
set. Every zero therefore has a positive actual affine period. This
derives the zero permutation from the regular/whole point maps. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffineZeroPermutation

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech LinearGroup Set Function
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {A : SL2} (φ : AffineAutomorphism q A)

theorem regular_maps (z : X) (hz : z ∈ regularSet q) : φ.surface z ∈ regularSet q := by
  let x : Regular q := ⟨z, hz⟩
  have hval := φ.value x
  exact hval ▸ (φ.regular x).property

theorem regular_iff (z : X) : φ.surface z ∈ regularSet q ↔ z ∈ regularSet q := by
  constructor
  · intro hz
    have hi := regular_maps q (AffineAutomorphism.inverse q φ) (φ.surface z) hz
    simpa only [AffineAutomorphism.inverse, Homeomorph.symm_apply_apply] using hi
  · exact regular_maps q φ z

theorem zero_iff (z : X) : φ.surface z ∈ zeroSet q ↔ z ∈ zeroSet q := by
  simpa only [regularSet, mem_compl_iff, not_not] using not_congr (regular_iff q φ z)

def zeroHomeomorph : zeroSet q ≃ₜ zeroSet q :=
  φ.surface.subtype (p := fun z => z ∈ zeroSet q) (q := fun z => z ∈ zeroSet q) (fun z => (zero_iff q φ z).symm)

theorem zero_periodic (z : X) (hz : z ∈ zeroSet q) : ∃ n : ℕ, 0 < n ∧ (φ.surface^[n]) z = z := by
  let : Finite (zeroSet q) := (zeroSet_finite q).to_subtype
  let f : zeroSet q → zeroSet q := zeroHomeomorph q φ
  have hinj : Injective f := (zeroHomeomorph q φ).injective
  have hval : Semiconj (Subtype.val : zeroSet q → X) f φ.surface := fun _ => rfl
  obtain ⟨n, hn, hperiod⟩ := hinj.mem_periodicPts (⟨z, hz⟩ : zeroSet q)
  exact ⟨n, hn, hperiod.map hval⟩

end VeechDichotomy.NativeAffineZeroPermutation
