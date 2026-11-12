module

public import VeechDichotomy.KoopmanMeanErgodic

/-! The actual Koopman mean is unchanged by applying its preserving
map to an observable. Commutation of the actual finite averages and
continuity identify the limits; no extra projection-invariance axiom. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KoopmanMeanShift

open MeasureTheory Filter Topology Finset KoopmanMeanErgodic

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Ω) (hf : MeasurePreserving f μ μ)

theorem average_operator (g : Space μ) (n : ℕ) :
    average μ f hf (operator μ f hf g) n = operator μ f hf (average μ f hf g n) := by
  unfold average birkhoffAverage birkhoffSum
  simp only [id_eq, map_smul, map_sum]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem mean_operator (g : Space μ) :
    limit μ f hf (operator μ f hf g) = limit μ f hf g := by
  have hu := (operator μ f hf).continuous.continuousAt.tendsto.comp (tendsto_average μ f hf g)
  have ha : Tendsto (average μ f hf (operator μ f hf g)) atTop (𝓝 (limit μ f hf g)) := by
    have h := Tendsto.congr (fun n => (average_operator μ f hf g n).symm) hu
    simpa only [limit_fixed] using h
  exact tendsto_nhds_unique (tendsto_average μ f hf (operator μ f hf g)) ha

theorem mean_operator_iterate (g : Space μ) (n : ℕ) :
    limit μ f hf ((operator μ f hf)^[n] g) = limit μ f hf g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', mean_operator, ih]

end VeechDichotomy.KoopmanMeanShift
