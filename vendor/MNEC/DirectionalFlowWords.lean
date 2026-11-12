module

public import MNEC.DirectionalBallCharts
public import MNEC.BallTrajectoryDomains
public import MNEC.RegularCoordinateArea
public import MNEC.DirectionalCompleteAction

@[expose] public section

/-!
# Finite words of actual convex-ball directional flow steps

Each letter consists of a proved convex physical ball chart and a real
time. Words execute their letters in order. Their partial homeomorphisms,
open sources, and image-area equalities follow by finite composition.
Every point in a word source is proved to lie in the actual native maximal
trajectory domain at the summed time, and the word map equals that native
trajectory. Convex-ball native interval proofs are used for every letter;
mere membership of two endpoints in a general chart is not used.
-/

noncomputable section

namespace MNEC.DirectionalFlowWords

open LatticeTorus RegularChartedSpace DirectionalBallCharts RegularTopologyArea
open DirectionalMaximalCurves MeasureTheory Set Topology Function
open scoped ENNReal Classical

section Composition

variable {σ X : Type*} [TopologicalSpace X]

def compose (maps : σ → OpenPartialHomeomorph X X) : List σ → OpenPartialHomeomorph X X
  | [] => OpenPartialHomeomorph.refl X
  | a :: W => (maps a).trans (compose maps W)

def duration (times : σ → ℝ) : List σ → ℝ
  | [] => 0
  | a :: W => times a + duration times W

theorem compose_append (maps : σ → OpenPartialHomeomorph X X) (W Z : List σ) :
    compose maps (W ++ Z) = (compose maps W).trans (compose maps Z) := by
  induction W with
  | nil => simp only [List.nil_append, compose, OpenPartialHomeomorph.refl_trans]
  | cons a W ih =>
    simp only [List.cons_append, compose, ih, OpenPartialHomeomorph.trans_assoc]

theorem duration_append (times : σ → ℝ) (W Z : List σ) :
    duration times (W ++ Z) = duration times W + duration times Z := by
  induction W with
  | nil => simp only [List.nil_append, duration, zero_add]
  | cons a W ih => simp only [List.cons_append, duration, ih, add_assoc]

variable [MeasurableSpace X] [BorelSpace X]

theorem compose_image_area (μ : Measure X) (maps : σ → OpenPartialHomeomorph X X)
    (hstep : ∀ a (V : Set X), MeasurableSet V → V ⊆ (maps a).source → μ (maps a '' V) = μ V)
    (W : List σ) (V : Set X) (hV : MeasurableSet V) (hsub : V ⊆ (compose maps W).source) :
    μ (compose maps W '' V) = μ V := by
  induction W generalizing V with
  | nil =>
    change μ ((id : X → X) '' V) = μ V
    rw [Set.image_id]
  | cons a W ih =>
    have hfirst : V ⊆ (maps a).source := fun x hx => (hsub hx).1
    have hrest : maps a '' V ⊆ (compose maps W).source := by
      rintro y ⟨x, hx, rfl⟩
      exact (hsub hx).2
    have himage : compose maps (a :: W) '' V = compose maps W '' (maps a '' V) := by
      change (fun x => compose maps W (maps a x)) '' V = compose maps W '' (maps a '' V)
      exact (Set.image_image _ _ V).symm
    rw [himage, ih _ (OffSlitChartArea.chart_image_measurable (maps a) V hV hfirst) hrest,
      hstep a V hV hfirst]

end Composition

section ActualBallWords

variable {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}

abbrev Step (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) := BallChart hw₁ hw₂ × ℝ

def elapsed (W : List (Step hw₁ hw₂)) : ℝ := duration (fun S => S.2) W

def stepMap (v : Plane) (S : Step hw₁ hw₂) :
    OpenPartialHomeomorph (Regular L₁ L₂ w) (Regular L₁ L₂ w) :=
  DirectionalBallCharts.timeMap S.1 v S.2

def wordMap (v : Plane) (W : List (Step hw₁ hw₂)) :
    OpenPartialHomeomorph (Regular L₁ L₂ w) (Regular L₁ L₂ w) := compose (stepMap v) W

@[simp] theorem elapsed_nil : elapsed ([] : List (Step hw₁ hw₂)) = 0 := rfl

@[simp] theorem elapsed_cons (S : Step hw₁ hw₂) (W : List (Step hw₁ hw₂)) :
    elapsed (S :: W) = S.2 + elapsed W := rfl

theorem elapsed_append (W Z : List (Step hw₁ hw₂)) : elapsed (W ++ Z) = elapsed W + elapsed Z :=
  duration_append _ W Z

@[simp] theorem elapsed_singleton (S : Step hw₁ hw₂) : elapsed [S] = S.2 := by
  rw [elapsed_cons, elapsed_nil, add_zero]

@[simp] theorem wordMap_nil (v : Plane) : wordMap v ([] : List (Step hw₁ hw₂)) =
    OpenPartialHomeomorph.refl (Regular L₁ L₂ w) := rfl

theorem wordMap_cons (v : Plane) (S : Step hw₁ hw₂) (W : List (Step hw₁ hw₂)) :
    wordMap v (S :: W) = (DirectionalBallCharts.timeMap S.1 v S.2).trans (wordMap v W) := rfl

@[simp] theorem wordMap_singleton (v : Plane) (S : Step hw₁ hw₂) :
    wordMap v [S] = DirectionalBallCharts.timeMap S.1 v S.2 := by
  rw [wordMap_cons, wordMap_nil, OpenPartialHomeomorph.trans_refl]

theorem wordMap_append (v : Plane) (W Z : List (Step hw₁ hw₂)) :
    wordMap v (W ++ Z) = (wordMap v W).trans (wordMap v Z) := compose_append _ W Z

theorem wordMap_append_apply (v : Plane) (W Z : List (Step hw₁ hw₂)) (x : Regular L₁ L₂ w) :
    wordMap v (W ++ Z) x = wordMap v Z (wordMap v W x) := by rw [wordMap_append]; rfl

theorem mem_wordMap_append_source (v : Plane) (W Z : List (Step hw₁ hw₂)) (x : Regular L₁ L₂ w) :
    x ∈ (wordMap v (W ++ Z)).source ↔
      x ∈ (wordMap v W).source ∧ wordMap v W x ∈ (wordMap v Z).source := by
  rw [wordMap_append]
  rfl

theorem word_source_open (v : Plane) (W : List (Step hw₁ hw₂)) : IsOpen (wordMap v W).source :=
  (wordMap v W).open_source

theorem ball_model_image_area (B : BallChart hw₁ hw₂) (V : Set Plane)
    (hV : MeasurableSet V) (hsub : V ⊆ (model B).source) :
    regularArea L₁ L₂ w (model B '' V) = volume V := by
  change regularArea L₁ L₂ w (RegularCoordinateArea.regularModel hw₁ hw₂ B.index '' V) = _
  apply RegularCoordinateArea.regularModel_area_image hw₁ hw₂ B.index V hV
  intro p hp
  exact B.ball_subset ((model_source B) ▸ hsub hp)

theorem ball_timeMap_image_area (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ)
    (V : Set (Regular L₁ L₂ w)) (hV : MeasurableSet V)
    (hsub : V ⊆ (DirectionalBallCharts.timeMap B v t).source) :
    regularArea L₁ L₂ w (DirectionalBallCharts.timeMap B v t '' V) = regularArea L₁ L₂ w V :=
  RegularCoordinateArea.translationTimeMap_image_area (regularArea L₁ L₂ w) (model B)
    (ball_model_image_area B) v t V hV hsub

theorem word_image_measurable (v : Plane) (W : List (Step hw₁ hw₂))
    (V : Set (Regular L₁ L₂ w)) (hV : MeasurableSet V) (hsub : V ⊆ (wordMap v W).source) :
    MeasurableSet (wordMap v W '' V) := OffSlitChartArea.chart_image_measurable _ V hV hsub

theorem word_image_area (v : Plane) (W : List (Step hw₁ hw₂))
    (V : Set (Regular L₁ L₂ w)) (hV : MeasurableSet V) (hsub : V ⊆ (wordMap v W).source) :
    regularArea L₁ L₂ w (wordMap v W '' V) = regularArea L₁ L₂ w V :=
  compose_image_area _ (stepMap v)
    (fun S => ball_timeMap_image_area S.1 v S.2) W V hV hsub

/-- Finite valid ball steps remain in the actual maximal native domain
at the summed time and compute precisely its native trajectory. -/
theorem word_native_identification (v : Plane) (W : List (Step hw₁ hw₂))
    (x : Regular L₁ L₂ w) (hx : x ∈ (wordMap v W).source) :
    elapsed W ∈ domain hw₁ hw₂ v x ∧ wordMap v W x = trajectory hw₁ hw₂ v x (elapsed W) := by
  induction W generalizing x with
  | nil =>
    refine ⟨zero_mem_domain hw₁ hw₂ v x, ?_⟩
    exact (trajectory_initial hw₁ hw₂ v x).symm
  | cons S W ih =>
    have hxFirst : x ∈ (DirectionalBallCharts.timeMap S.1 v S.2).source := hx.1
    have hxRest : DirectionalBallCharts.timeMap S.1 v S.2 x ∈ (wordMap v W).source := hx.2
    have ht := BallTrajectoryDomains.timeMap_time_mem_domain S.1 v S.2 x hxFirst
    have hvalue := BallTrajectoryDomains.timeMap_eq_trajectory S.1 v S.2 x hxFirst
    obtain ⟨hs, hrest⟩ := ih _ hxRest
    have hs' : elapsed W ∈ domain hw₁ hw₂ v (trajectory hw₁ hw₂ v x S.2) := by
      rw [← hvalue]
      exact hs
    have htotal : elapsed W + S.2 ∈ domain hw₁ hw₂ v x := by
      have h := hs'
      rw [DirectionalCompleteAction.domain_at_time hw₁ hw₂ v x S.2 ht] at h
      exact h
    constructor
    · simpa only [elapsed_cons, add_comm] using htotal
    · change wordMap v W (DirectionalBallCharts.timeMap S.1 v S.2 x) =
        trajectory hw₁ hw₂ v x (S.2 + elapsed W)
      calc
        wordMap v W (DirectionalBallCharts.timeMap S.1 v S.2 x) =
            trajectory hw₁ hw₂ v (DirectionalBallCharts.timeMap S.1 v S.2 x) (elapsed W) := hrest
        _ = trajectory hw₁ hw₂ v (trajectory hw₁ hw₂ v x S.2) (elapsed W) := by rw [hvalue]
        _ = trajectory hw₁ hw₂ v x (elapsed W + S.2) :=
          DirectionalCompleteAction.trajectory_add hw₁ hw₂ v x S.2 ht (elapsed W) hs'
        _ = trajectory hw₁ hw₂ v x (S.2 + elapsed W) := by rw [add_comm]

theorem word_time_mem_domain (v : Plane) (W : List (Step hw₁ hw₂))
    (x : Regular L₁ L₂ w) (hx : x ∈ (wordMap v W).source) : elapsed W ∈ domain hw₁ hw₂ v x :=
  (word_native_identification v W x hx).1

theorem wordMap_eq_trajectory (v : Plane) (W : List (Step hw₁ hw₂))
    (x : Regular L₁ L₂ w) (hx : x ∈ (wordMap v W).source) :
    wordMap v W x = trajectory hw₁ hw₂ v x (elapsed W) := (word_native_identification v W x hx).2

end ActualBallWords

end MNEC.DirectionalFlowWords
