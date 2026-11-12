module

public import VeechDichotomy.PositiveMassFixedReturns
public import VeechDichotomy.ProperFiberLimits

/-! The positive-mass and proper-family arguments produce a FIXED
point in any conull set, and an actual limit of its images in the exact
limit fiber. All return times use one strictly increasing subsequence. -/

@[expose] public section

namespace VeechDichotomy.PositiveMassFiberLimits

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {X T P : Type*} [MeasurableSpace X]
  [TopologicalSpace T] [FirstCountableTopology T] [TopologicalSpace P] [T2Space P]

theorem fixed_point (μ : Measure X) [IsFiniteMeasure μ]
    (π : T → P) (hπ : IsProperMap π) (f : ℕ → X → T)
    (p : ℕ → P) (p₀ : P) (hp : Tendsto p atTop (𝓝 p₀)) (hproj : ∀ n x, π (f n x) = p n)
    {C : Set T} (hC : IsClosed C) (hm : ∀ n, MeasurableSet (f n ⁻¹' C))
    {δ : ℝ≥0∞} (hδpos : 0 < δ) (hδ : ∃ᶠ n in atTop, δ ≤ μ (f n ⁻¹' C))
    {E : Set X} (hE : μ Eᶜ = 0) :
    ∃ x ∈ E, ∃ y ∈ C, π y = p₀ ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (fun n => f (σ n) x) atTop (𝓝 y) := by
  obtain ⟨x, hxE, hxret⟩ := PositiveMassFixedReturns.exists_fixed_return μ _ hm hδpos hδ hE
  have hplim : Tendsto (fun n => π (f n x)) atTop (𝓝 p₀) := by
    simpa only [hproj] using hp
  obtain ⟨y, hyC, hy, σ, hσ, hlim⟩ := ProperFiberLimits.subsequence_in_closed π hπ (fun n => f n x) p₀ hplim hC hxret
  exact ⟨x, hxE, y, hyC, hy, σ, hσ, hlim⟩

end VeechDichotomy.PositiveMassFiberLimits
