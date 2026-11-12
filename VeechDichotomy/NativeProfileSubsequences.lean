module

public import VeechDichotomy.NativeVariableSourceProfiles

/-! Full native varying-endpoint profiles survive EVERY further
strictly increasing subsequence. Rational profiles are recovered from
the proved stable property, restricted, and used to reconstruct the
full property, including endpoint sequences chosen only on the subsequence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeProfileSubsequences

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Set Filter Topology VaryingOccupationProfiles NativeVariableSourceProfiles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem rational_of_stable (B : Set (CompleteOrbits q v)) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (x : CompleteOrbits q v) (m : ℝ) (hs : StableProfile q v B R x m) (a : PositiveRational) (backward : Bool) :
    Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward ((a.val : ℝ) * R k) x) atTop (𝓝 m) := by
  have hratio : Tendsto (fun k => ((a.val : ℝ) * R k) / R k) atTop (𝓝 (a.val : ℝ)) := by
    have hpos : ∀ᶠ k in atTop, 0 < R k := hR.eventually (eventually_gt_atTop (0 : ℝ))
    have heq : (fun _ : ℕ => (a.val : ℝ)) =ᶠ[atTop] (fun k => ((a.val : ℝ) * R k) / R k) := by
      filter_upwards [hpos] with k hk
      exact (mul_div_cancel_right₀ (a.val : ℝ) hk.ne').symm
    exact Tendsto.congr' heq tendsto_const_nhds
  exact hs.1 backward _ (a.val : ℝ) hratio (by exact_mod_cast a.property)

theorem subsequence (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (x : CompleteOrbits q v) (m : ℝ) (hs : StableProfile q v B R x m) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    StableProfile q v B (R ∘ σ) x m := by
  apply NativeVariableSourceProfiles.of_rational q v B hB (R ∘ σ) (hR.comp hσ.tendsto_atTop) x m
  intro a backward
  exact (rational_of_stable q v B R hR x m hs a backward).comp hσ.tendsto_atTop

end VeechDichotomy.NativeProfileSubsequences
