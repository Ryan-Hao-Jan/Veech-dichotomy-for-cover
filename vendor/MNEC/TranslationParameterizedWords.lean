module

public import MNEC.TranslationFlowWords
public import MNEC.ParameterizedFlowWords

/-!
# Velocity-dependent accepted physical words

For any fixed finite word, acceptance is open jointly in physical velocity
and initial point, and evaluation is continuous on that actual source.
These are direct physical-chart formulas and finite composition, rather
than a parameter-dependence premise for native ODE solutions.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationParameterizedWords

open LatticeTorus TranslationBallCharts TranslationFlowWords Set Topology
open ParameterizedFlowWords (parameterSource parameterValue localValid localStep)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

theorem ball_localValid_iff (B : BallChart X) (p : Plane × ℝ × X) :
    p ∈ localValid (model B) ↔ p.2.2 ∈ (timeMap B p.1 p.2.1).source := by
  rw [mem_timeMap_source]
  change (_ ∧ _ ∈ (model B).source) ↔ (_ ∧ _ ∈ Metric.ball B.center B.radius)
  rw [model_source]

theorem parameter_step (S : Step X) :
    IsOpen (parameterSource (fun v => stepMap v S)) ∧
      ContinuousOn (parameterValue (fun v => stepMap v S)) (parameterSource (fun v => stepMap v S)) := by
  let H : Plane × X → Plane × ℝ × X := fun p => (p.1, S.2, p.2)
  have hH : Continuous H := continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hsource : parameterSource (fun v => stepMap v S) = H ⁻¹' localValid (model S.1) := by
    ext p
    exact (ball_localValid_iff S.1 (H p)).symm
  rw [hsource]
  refine ⟨(ParameterizedFlowWords.localValid_open (model S.1)).preimage hH, ?_⟩
  have hvalue : parameterValue (fun v => stepMap v S) = fun p => localStep (model S.1) (H p) := by funext p; rfl
  rw [hvalue]
  exact (ParameterizedFlowWords.continuousOn_localStep (model S.1)).comp hH.continuousOn (fun _ hp => hp)

theorem parameter_word (W : List (Step X)) :
    IsOpen (parameterSource (fun v => wordMap v W)) ∧
      ContinuousOn (parameterValue (fun v => wordMap v W)) (parameterSource (fun v => wordMap v W)) := by
  induction W with
  | nil =>
    change IsOpen (univ : Set (Plane × X)) ∧ ContinuousOn Prod.snd univ
    exact ⟨isOpen_univ, continuous_snd.continuousOn⟩
  | cons S W ih =>
    exact ParameterizedFlowWords.parameter_trans (fun v => stepMap v S) (fun v => wordMap v W)
      (parameter_step S).1 (parameter_step S).2 ih.1 ih.2

theorem parameter_word_continuousAt (W : List (Step X)) (p : Plane × X) (hp : p.2 ∈ (wordMap p.1 W).source) :
    ContinuousAt (parameterValue (fun v => wordMap v W)) p :=
  ((parameter_word W).2 p hp).continuousAt ((parameter_word W).1.mem_nhds hp)

end MNEC.TranslationParameterizedWords

