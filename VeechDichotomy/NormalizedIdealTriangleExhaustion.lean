module

public import VeechDichotomy.NormalizedIdealTriangleArea
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Monotone exhaustion of the normalized fully ideal triangle by actual
one-ideal triangles with finite vertices. The literal coordinate regions
exhaust its open strip, and actual measure continuity plus the proved
area formula compute the open-strip area as pi. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIdealTriangleExhaustion

open NormalizedIdealTriangleCoordinates NormalizedIdealTriangleArea Set Filter Topology MeasureTheory
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def cutoff (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

theorem cutoff_nonneg (n : ℕ) : 0 ≤ cutoff n := by
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hd).mpr (by linarith only [hn])
  exact sub_nonneg.mpr hdiv

theorem cutoff_lt_one (n : ℕ) : cutoff n < 1 := by
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  dsimp only [cutoff]
  linarith only [hp]

theorem cutoff_monotone : Monotone cutoff := by
  intro m n hmn
  have hd : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  have hr := one_div_le_one_div_of_le (show 0 < (m : ℝ) + 1 by positivity) hd
  dsimp only [cutoff]
  linarith only [hr]

theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 (1 : ℝ)) := by
  simpa only [sub_zero] using! (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def openRegion : Set ℍ := {z | -1 < z.re ∧ z.re < 1 ∧ height z.re ≤ z.im}

theorem regions_monotone : Monotone (fun n : ℕ => region (-cutoff n) (cutoff n)) := by
  intro m n hmn z hz
  have h := cutoff_monotone hmn
  exact ⟨⟨(neg_le_neg h).trans hz.1.1, hz.1.2.trans h⟩, hz.2⟩

theorem union_regions : (⋃ n : ℕ, region (-cutoff n) (cutoff n)) = openRegion := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    have hr := cutoff_lt_one n
    refine ⟨?_, ?_, hn.2⟩
    · linarith only [hr, hn.1.1]
    · linarith only [hr, hn.1.2]
  · intro z hz
    have h₀ : ∀ᶠ n in atTop, z.re < cutoff n := cutoff_tendsto (eventually_gt_nhds hz.2.1)
    have h₁ : ∀ᶠ n in atTop, -z.re < cutoff n := cutoff_tendsto (eventually_gt_nhds (by linarith only [hz.1]))
    obtain ⟨n, hn₀, hn₁⟩ := (h₀.and h₁).exists
    exact mem_iUnion.mpr ⟨n, ⟨⟨by linarith only [hn₁], hn₀.le⟩, hz.2.2⟩⟩

theorem openRegion_area : volume openRegion = ENNReal.ofReal Real.pi := by
  have hlim : Tendsto (fun n : ℕ => volume (region (-cutoff n) (cutoff n))) atTop (𝓝 (volume openRegion)) := by
    simpa only [Function.comp_def, union_regions] using
      (tendsto_measure_iUnion_atTop (μ := (volume : Measure ℍ)) regions_monotone)
  have harc := (Real.continuous_arcsin.tendsto (1 : ℝ)).comp cutoff_tendsto
  have hdouble := (tendsto_const_nhds (x := (2 : ℝ))).mul harc
  have hval : (2 : ℝ) * Real.arcsin 1 = Real.pi := by rw [Real.arcsin_one]; ring
  have hreal : Tendsto (fun n : ℕ => Real.arcsin (cutoff n) - Real.arcsin (-cutoff n)) atTop (𝓝 Real.pi) := by
    have heq : (fun n : ℕ => Real.arcsin (cutoff n) - Real.arcsin (-cutoff n)) =
        fun n => 2 * Real.arcsin (cutoff n) := by
      funext n
      rw [Real.arcsin_neg]
      ring
    rw [heq]
    simpa only [hval] using! hdouble
  have hlim₂ : Tendsto (fun n : ℕ => volume (region (-cutoff n) (cutoff n))) atTop (𝓝 (ENNReal.ofReal Real.pi)) := by
    have heq : (fun n : ℕ => volume (region (-cutoff n) (cutoff n))) =
        fun n => ENNReal.ofReal (Real.arcsin (cutoff n) - Real.arcsin (-cutoff n)) := by
      funext n
      exact area_formula (by linarith only [cutoff_lt_one n]) (cutoff_lt_one n) (by linarith only [cutoff_nonneg n])
    rw [heq]
    exact (ENNReal.continuous_ofReal.tendsto Real.pi).comp hreal
  exact tendsto_nhds_unique hlim hlim₂

end VeechDichotomy.NormalizedIdealTriangleExhaustion
