module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Invariant probabilities and their uniqueness transfer through an
actual measurable conjugacy. This is a measure-theoretic transport lemma;
it contains no translation-surface or recurrence hypothesis.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.InvariantProbabilityTransport

open MeasureTheory Set

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

def InvariantFor (F : ℝ → U → U) (μ : Measure U) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t : ℝ, MeasurePreserving (F t) μ μ

theorem map_invariant (e : U ≃ᵐ V) (F : ℝ → U → U) (G : ℝ → V → V)
    (hconj : ∀ t x, e (F t x) = G t (e x)) (hG : ∀ t, Measurable (G t))
    {μ : Measure U} (hμ : InvariantFor F μ) : InvariantFor G (μ.map e) := by
  refine ⟨?_, fun t => ⟨hG t, ?_⟩⟩
  · constructor
    rw [Measure.map_apply e.measurable MeasurableSet.univ, preimage_univ]
    exact hμ.1.measure_univ
  · rw [Measure.map_map (hG t) e.measurable]
    have heq : G t ∘ e = e ∘ F t := funext (fun x => (hconj t x).symm)
    rw [heq, ← Measure.map_map e.measurable (hμ.2 t).measurable, (hμ.2 t).map_eq]

theorem inverse_conjugacy (e : U ≃ᵐ V) (F : ℝ → U → U) (G : ℝ → V → V)
    (hconj : ∀ t x, e (F t x) = G t (e x)) :
    ∀ t y, e.symm (G t y) = F t (e.symm y) := by
  intro t y
  apply e.injective
  rw [e.apply_symm_apply, hconj, e.apply_symm_apply]

theorem existsUnique_map (e : U ≃ᵐ V) (F : ℝ → U → U) (G : ℝ → V → V)
    (hconj : ∀ t x, e (F t x) = G t (e x))
    (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t))
    (hunique : ∃! μ : Measure U, InvariantFor F μ) :
    ∃! ν : Measure V, InvariantFor G ν := by
  obtain ⟨μ, hμ, huniq⟩ := hunique
  refine ⟨μ.map e, map_invariant e F G hconj hG hμ, ?_⟩
  intro ν hν
  have hback := map_invariant e.symm G F (inverse_conjugacy e F G hconj) hF hν
  have heq := congrArg (Measure.map e) (huniq (ν.map e.symm) hback)
  simpa only [MeasurableEquiv.map_map_symm] using heq

theorem existsUnique_iff (e : U ≃ᵐ V) (F : ℝ → U → U) (G : ℝ → V → V)
    (hconj : ∀ t x, e (F t x) = G t (e x))
    (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t)) :
    (∃! μ : Measure U, InvariantFor F μ) ↔ ∃! ν : Measure V, InvariantFor G ν :=
  ⟨existsUnique_map e F G hconj hF hG,
    existsUnique_map e.symm G F (inverse_conjugacy e F G hconj) hG hF⟩

theorem invariantFor_clock_iff (F : ℝ → U → U) (clock : ℝ → ℝ)
    (hclock : Function.Surjective clock) (μ : Measure U) :
    InvariantFor (fun t => F (clock t)) μ ↔ InvariantFor F μ := by
  constructor
  · intro h
    refine ⟨h.1, fun t => ?_⟩
    obtain ⟨s, rfl⟩ := hclock t
    exact h.2 s
  · intro h
    exact ⟨h.1, fun t => h.2 (clock t)⟩

theorem existsUnique_clock_iff (F : ℝ → U → U) (clock : ℝ → ℝ)
    (hclock : Function.Surjective clock) :
    (∃! μ : Measure U, InvariantFor (fun t => F (clock t)) μ) ↔
      ∃! μ : Measure U, InvariantFor F μ := by
  apply existsUnique_congr
  intro μ
  exact invariantFor_clock_iff F clock hclock μ

end VeechDichotomy.InvariantProbabilityTransport
