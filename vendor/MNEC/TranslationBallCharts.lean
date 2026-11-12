module

public import MNEC.TranslationAtlasCurves
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Module

/-!
# Accepted physical ball steps in any native translation atlas

Ball data consist only of an actual atlas chart and a positive physical
ball contained in its target. Convexity verifies the entire intervening
line segment. Native maximality identifies each accepted step with the
independently constructed maximal curve; no flow premise is stored in the
ball data.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationBallCharts

open LatticeTorus Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

structure BallChart (X : Type*) [TopologicalSpace X] [ChartedSpace Plane X] where
  chart : OpenPartialHomeomorph X Plane
  mem_atlas : chart ∈ atlas Plane X
  center : Plane
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball center radius ⊆ chart.target

def model (B : BallChart X) : OpenPartialHomeomorph Plane X := B.chart.symm.restr (Metric.ball B.center B.radius)

theorem model_source (B : BallChart X) : (model B).source = Metric.ball B.center B.radius := by
  unfold model
  rw [B.chart.symm.restr_source' _ Metric.isOpen_ball]
  exact inter_eq_right.mpr B.ball_subset

theorem model_apply (B : BallChart X) (p : Plane) : model B p = B.chart.symm p := rfl
theorem model_symm_apply (B : BallChart X) (x : X) : (model B).symm x = B.chart x := rfl

theorem target_subset_chartSource (B : BallChart X) : (model B).target ⊆ B.chart.source := by
  intro x hx
  have hp : (model B).symm x ∈ Metric.ball B.center B.radius := (model_source B) ▸ (model B).map_target hx
  have hbase := B.chart.map_target (B.ball_subset hp)
  have heq : B.chart.symm (B.chart x) = x := (model B).right_inv hx
  rw [model_symm_apply] at hbase
  rwa [heq] at hbase

theorem exists_ballChart_at (x : X) : ∃ B : BallChart X, x ∈ (model B).target := by
  let e := chartAt Plane x
  have hx : x ∈ e.source := mem_chart_source Plane x
  let p := e x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target p (e.map_source hx)
  let B : BallChart X := ⟨e, chart_mem_atlas Plane x, p, r, hr, hball⟩
  have hp : p ∈ (model B).source := by rw [model_source]; exact Metric.mem_ball_self hr
  have hmem := (model B).map_source hp
  have heq : model B p = x := e.left_inv hx
  exact ⟨B, heq ▸ hmem⟩

def timeDomain (B : BallChart X) (v : Plane) (x : X) : Set ℝ :=
  {t | (model B).symm x + t • v ∈ Metric.ball B.center B.radius}

def curve (B : BallChart X) (v : Plane) (x : X) (t : ℝ) : X := model B ((model B).symm x + t • v)

theorem curve_eq_generic (B : BallChart X) (v : Plane) (x : X) :
    curve B v x = TranslationAtlasCurves.curve B.chart v x := rfl

theorem timeDomain_open (B : BallChart X) (v : Plane) (x : X) : IsOpen (timeDomain B v x) :=
  Metric.isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))

theorem timeDomain_convex (B : BallChart X) (v : Plane) (x : X) : Convex ℝ (timeDomain B v x) := by
  intro s hs t ht a b ha hb hab
  have h := convex_ball B.center B.radius hs ht ha hb hab
  change (model B).symm x + (a * s + b * t) • v ∈ Metric.ball B.center B.radius
  have heq : a • ((model B).symm x + s • v) + b • ((model B).symm x + t • v) =
      (model B).symm x + (a * s + b * t) • v := by
    calc
      _ = (a + b) • (model B).symm x + (a * s + b * t) • v := by module
      _ = _ := by rw [hab, one_smul]
  rwa [heq] at h

theorem timeDomain_subset_generic (B : BallChart X) (v : Plane) (x : X) :
    timeDomain B v x ⊆ TranslationAtlasCurves.timeDomain B.chart v x := fun _ ht => B.ball_subset ht

theorem zero_mem_timeDomain (B : BallChart X) (v : Plane) (x : X) (hx : x ∈ (model B).target) :
    0 ∈ timeDomain B v x := by
  change (model B).symm x + (0 : ℝ) • v ∈ Metric.ball B.center B.radius
  rw [zero_smul, add_zero]
  exact (model_source B) ▸ (model B).map_target hx

theorem curve_zero (B : BallChart X) (v : Plane) (x : X) (hx : x ∈ (model B).target) : curve B v x 0 = x := by
  change model B ((model B).symm x + (0 : ℝ) • v) = x
  rw [zero_smul, add_zero]
  exact (model B).right_inv hx

def timeMap (B : BallChart X) (v : Plane) (t : ℝ) : OpenPartialHomeomorph X X :=
  ((model B).symm.transHomeomorph (Homeomorph.addRight (t • v))).trans (model B)

theorem timeMap_apply (B : BallChart X) (v : Plane) (t : ℝ) (x : X) : timeMap B v t x = curve B v x t := rfl

theorem mem_timeMap_source (B : BallChart X) (v : Plane) (t : ℝ) (x : X) :
    x ∈ (timeMap B v t).source ↔ x ∈ (model B).target ∧ t ∈ timeDomain B v x := by
  change (x ∈ (model B).target ∧ (model B).symm x + t • v ∈ (model B).source) ↔ _
  rw [model_source]
  rfl

theorem coordinates_curve (B : BallChart X) (v : Plane) (x : X) (t : ℝ) (ht : t ∈ timeDomain B v x) :
    (model B).symm (curve B v x t) = (model B).symm x + t • v := by
  apply (model B).left_inv
  exact (model_source B).symm ▸ ht

theorem curve_mem_target (B : BallChart X) (v : Plane) (x : X) (t : ℝ) (ht : t ∈ timeDomain B v x) :
    curve B v x t ∈ (model B).target := (model B).map_source ((model_source B).symm ▸ ht)

theorem reverse_step_source (B : BallChart X) (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (timeMap B v t).source) :
    timeMap B v t x ∈ (timeMap B v (-t)).source := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  rw [timeMap_apply, mem_timeMap_source]
  refine ⟨curve_mem_target B v x t ht, ?_⟩
  change (model B).symm (curve B v x t) + (-t) • v ∈ Metric.ball B.center B.radius
  rw [coordinates_curve B v x t ht]
  have heq : ((model B).symm x + t • v) + (-t) • v = (model B).symm x := by simp [neg_smul, add_assoc]
  rw [heq]
  exact (model_source B) ▸ (model B).map_target hxB

theorem reverse_step_value (B : BallChart X) (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (timeMap B v t).source) :
    timeMap B v (-t) (timeMap B v t x) = x := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  change model B ((model B).symm (curve B v x t) + (-t) • v) = x
  rw [coordinates_curve B v x t ht]
  have heq : ((model B).symm x + t • v) + (-t) • v = (model B).symm x := by simp [neg_smul, add_assoc]
  rw [heq]
  exact (model B).right_inv hxB

theorem segment_mem_timeDomain (B : BallChart X) (v : Plane) (x : X) (hx : x ∈ (model B).target)
    (t : ℝ) (ht : t ∈ timeDomain B v x) : uIcc (0 : ℝ) t ⊆ timeDomain B v x :=
  (timeDomain_convex B v x).ordConnected.uIcc_subset (zero_mem_timeDomain B v x hx) ht

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X]

theorem isMIntegralCurveOn_curve (B : BallChart X) (v : Plane) (x : X) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve B v x) (TranslationAtlasField.field v) (timeDomain B v x) := by
  rw [curve_eq_generic]
  exact (TranslationAtlasCurves.isMIntegralCurveOn_curve B.chart B.mem_atlas v x).mono (timeDomain_subset_generic B v x)

variable [T2Space X]

theorem extends_ball_curve (B : BallChart X) (v : Plane) (x : X) (hx : x ∈ (model B).target) :
    timeDomain B v x ⊆ TranslationAtlasCurves.domain v x ∧
      EqOn (TranslationAtlasCurves.trajectory v x) (curve B v x) (timeDomain B v x) :=
  TranslationAtlasCurves.extends_every_open_interval v x (timeDomain B v x) (curve B v x) (timeDomain_open B v x)
    (timeDomain_convex B v x).ordConnected (zero_mem_timeDomain B v x hx) (curve_zero B v x hx) (isMIntegralCurveOn_curve B v x)

theorem timeMap_native_identification (B : BallChart X) (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (timeMap B v t).source) :
    t ∈ TranslationAtlasCurves.domain v x ∧ timeMap B v t x = TranslationAtlasCurves.trajectory v x t := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  exact ⟨(extends_ball_curve B v x hxB).1 ht, ((extends_ball_curve B v x hxB).2 ht).symm⟩

theorem timeMap_segment_in_chart (B : BallChart X) (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (timeMap B v t).source) :
    ∀ s ∈ uIcc (0 : ℝ) t, s ∈ TranslationAtlasCurves.domain v x ∧
      TranslationAtlasCurves.trajectory v x s ∈ (model B).target := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  intro s hs
  have hvalid := segment_mem_timeDomain B v x hxB t ht hs
  refine ⟨(extends_ball_curve B v x hxB).1 hvalid, ?_⟩
  rw [(extends_ball_curve B v x hxB).2 hvalid]
  exact curve_mem_target B v x s hvalid

end MNEC.TranslationBallCharts

