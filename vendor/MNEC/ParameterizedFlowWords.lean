module

public import MNEC.DirectionalFlowWords

@[expose] public section

/-!+# Velocity dependence of actual convex-ball flow words

For a fixed finite word of ball charts and times, its valid source is open
jointly in physical velocity and initial point. Its evaluation is jointly
continuous on that source. This uses the actual chart formulas and finite
composition, without a parameter-dependence assumption about ODE solutions.
-/

noncomputable section

namespace MNEC.ParameterizedFlowWords

open LatticeTorus RegularChartedSpace DirectionalBallCharts DirectionalFlowWords Set
open scoped Topology

section LocalModel

variable {X : Type*} [TopologicalSpace X]

def localValid (e : OpenPartialHomeomorph Plane X) : Set (Plane × ℝ × X) :=
  {p | p.2.2 ∈ e.target ∧ e.symm p.2.2 + p.2.1 • p.1 ∈ e.source}

def localStep (e : OpenPartialHomeomorph Plane X) (p : Plane × ℝ × X) : X :=
  e (e.symm p.2.2 + p.2.1 • p.1)

theorem localValid_open (e : OpenPartialHomeomorph Plane X) : IsOpen (localValid e) := by
  let A : Set (Plane × ℝ × X) := (fun p => p.2.2) ⁻¹' e.target
  let f : Plane × ℝ × X → Plane := fun p => e.symm p.2.2 + p.2.1 • p.1
  have hA : IsOpen A := e.open_target.preimage continuous_snd.snd
  have he : ContinuousOn (fun p : Plane × ℝ × X => e.symm p.2.2) A :=
    e.continuousOn_symm.comp continuous_snd.snd.continuousOn (fun _ hp => hp)
  have hf : ContinuousOn f A := he.add (continuous_snd.fst.smul continuous_fst).continuousOn
  change IsOpen (A ∩ f ⁻¹' e.source)
  exact hf.isOpen_inter_preimage hA e.open_source

theorem continuousOn_localStep (e : OpenPartialHomeomorph Plane X) :
    ContinuousOn (localStep e) (localValid e) := by
  let A : Set (Plane × ℝ × X) := (fun p => p.2.2) ⁻¹' e.target
  let f : Plane × ℝ × X → Plane := fun p => e.symm p.2.2 + p.2.1 • p.1
  have he : ContinuousOn (fun p : Plane × ℝ × X => e.symm p.2.2) A :=
    e.continuousOn_symm.comp continuous_snd.snd.continuousOn (fun _ hp => hp)
  have hf : ContinuousOn f A := he.add (continuous_snd.fst.smul continuous_fst).continuousOn
  change ContinuousOn (fun p => e (f p)) (A ∩ f ⁻¹' e.source)
  exact e.continuousOn.comp (hf.mono inter_subset_left) (fun _ hp => hp.2)

theorem continuousAt_localStep (e : OpenPartialHomeomorph Plane X)
    (p : Plane × ℝ × X) (hp : p ∈ localValid e) : ContinuousAt (localStep e) p :=
  (continuousOn_localStep e p hp).continuousAt ((localValid_open e).mem_nhds hp)

theorem zero_mem_localValid (e : OpenPartialHomeomorph Plane X) (v : Plane)
    (x : X) (hx : x ∈ e.target) : (v, 0, x) ∈ localValid e := by
  refine ⟨hx, ?_⟩
  simpa only [zero_smul, add_zero] using e.map_target hx

end LocalModel

section Composition

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

def parameterSource (F : P → OpenPartialHomeomorph X X) : Set (P × X) :=
  {p | p.2 ∈ (F p.1).source}

def parameterValue (F : P → OpenPartialHomeomorph X X) (p : P × X) : X := F p.1 p.2

theorem parameter_trans (F G : P → OpenPartialHomeomorph X X)
    (hFo : IsOpen (parameterSource F)) (hFc : ContinuousOn (parameterValue F) (parameterSource F))
    (hGo : IsOpen (parameterSource G)) (hGc : ContinuousOn (parameterValue G) (parameterSource G)) :
    IsOpen (parameterSource (fun p => (F p).trans (G p))) ∧
      ContinuousOn (parameterValue (fun p => (F p).trans (G p)))
        (parameterSource (fun p => (F p).trans (G p))) := by
  let H : P × X → P × X := fun p => (p.1, F p.1 p.2)
  have hH : ContinuousOn H (parameterSource F) := continuous_fst.continuousOn.prodMk hFc
  have hsource : parameterSource (fun p => (F p).trans (G p)) =
      parameterSource F ∩ H ⁻¹' parameterSource G := rfl
  rw [hsource]
  refine ⟨hH.isOpen_inter_preimage hFo hGo, ?_⟩
  exact hGc.comp (hH.mono inter_subset_left) (fun _ hp => hp.2)

end Composition

variable {L₁ L₂ : Lattice} {w : Plane}
variable {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}

theorem ball_localValid_iff (B : BallChart hw₁ hw₂) (p : Plane × ℝ × Regular L₁ L₂ w) :
    p ∈ localValid (model B) ↔
      p.2.2 ∈ (DirectionalBallCharts.timeMap B p.1 p.2.1).source := by
  rw [mem_timeMap_source]
  change (_ ∧ _ ∈ (model B).source) ↔ (_ ∧ _ ∈ Metric.ball B.center B.radius)
  rw [model_source]

theorem parameter_step (S : Step hw₁ hw₂) :
    IsOpen (parameterSource (fun v => stepMap v S)) ∧
      ContinuousOn (parameterValue (fun v => stepMap v S))
        (parameterSource (fun v => stepMap v S)) := by
  let H : Plane × Regular L₁ L₂ w → Plane × ℝ × Regular L₁ L₂ w :=
    fun p => (p.1, S.2, p.2)
  have hH : Continuous H := continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hsource : parameterSource (fun v => stepMap v S) = H ⁻¹' localValid (model S.1) := by
    ext p
    exact (ball_localValid_iff S.1 (H p)).symm
  rw [hsource]
  refine ⟨(localValid_open (model S.1)).preimage hH, ?_⟩
  have hvalue : parameterValue (fun v => stepMap v S) =
      fun p => localStep (model S.1) (H p) := by
    funext p
    rfl
  rw [hvalue]
  exact (continuousOn_localStep (model S.1)).comp hH.continuousOn (fun _ hp => hp)

theorem parameter_word (W : List (Step hw₁ hw₂)) :
    IsOpen (parameterSource (fun v => wordMap v W)) ∧
      ContinuousOn (parameterValue (fun v => wordMap v W))
        (parameterSource (fun v => wordMap v W)) := by
  induction W with
  | nil =>
    change IsOpen (univ : Set (Plane × Regular L₁ L₂ w)) ∧ ContinuousOn Prod.snd univ
    exact ⟨isOpen_univ, continuous_snd.continuousOn⟩
  | cons S W ih =>
    exact parameter_trans (fun v => stepMap v S) (fun v => wordMap v W)
      (parameter_step S).1 (parameter_step S).2 ih.1 ih.2

theorem parameter_word_continuousAt (W : List (Step hw₁ hw₂))
    (p : Plane × Regular L₁ L₂ w) (hp : p.2 ∈ (wordMap p.1 W).source) :
    ContinuousAt (parameterValue (fun v => wordMap v W)) p :=
  ((parameter_word W).2 p hp).continuousAt ((parameter_word W).1.mem_nhds hp)

end MNEC.ParameterizedFlowWords
