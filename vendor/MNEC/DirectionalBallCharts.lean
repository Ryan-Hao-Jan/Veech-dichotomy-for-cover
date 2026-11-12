module

public import MNEC.LocalDirectionalIntegralCurves
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Convex physical subcharts for genuine directional continuation

Each ball is contained in an actual regular physical chart. Its time domain
is open and convex, so a valid step includes the entire intervening time
segment. The native integral-curve proof is inherited from the actual
physical straight curves, not assumed as part of ball data.
-/

noncomputable section

namespace MNEC.DirectionalBallCharts

open LatticeTorus RegularChartedSpace RegularAtlasCoverage Set
open scoped Topology Manifold

structure BallChart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) where
  index : Index L₁ L₂ w
  center : Plane
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball center radius ⊆ (regularChart hw₁ hw₂ index).target

def model {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) : OpenPartialHomeomorph Plane (Regular L₁ L₂ w) :=
  (regularChart hw₁ hw₂ B.index).symm.restr (Metric.ball B.center B.radius)

theorem model_source {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) : (model B).source = Metric.ball B.center B.radius := by
  unfold model
  rw [(regularChart hw₁ hw₂ B.index).symm.restr_source' _ Metric.isOpen_ball]
  exact inter_eq_right.mpr B.ball_subset

theorem model_apply {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (p : Plane) :
    model B p = (regularChart hw₁ hw₂ B.index).symm p := rfl

theorem model_symm_apply {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (x : Regular L₁ L₂ w) :
    (model B).symm x = regularChart hw₁ hw₂ B.index x := rfl

theorem target_subset_chartSource {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w} (B : BallChart hw₁ hw₂) :
    (model B).target ⊆ (regularChart hw₁ hw₂ B.index).source := by
  intro x hx
  have hp : (model B).symm x ∈ Metric.ball B.center B.radius :=
    (model_source B) ▸ (model B).map_target hx
  have hbase := (regularChart hw₁ hw₂ B.index).map_target (B.ball_subset hp)
  have heq : (regularChart hw₁ hw₂ B.index).symm (regularChart hw₁ hw₂ B.index x) = x :=
    (model B).right_inv hx
  rw [model_symm_apply] at hbase
  rwa [heq] at hbase

theorem exists_ballChart_at {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (x : Regular L₁ L₂ w) :
    ∃ B : BallChart hw₁ hw₂, x ∈ (model B).target := by
  let i := chosenIndex hw₁ hw₂ x
  have hx : x ∈ (regularChart hw₁ hw₂ i).source := by
    rw [regularChart_source]
    exact chosenIndex_mem_target hw₁ hw₂ x
  let p := regularChart hw₁ hw₂ i x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (regularChart hw₁ hw₂ i).open_target p
    ((regularChart hw₁ hw₂ i).map_source hx)
  let B : BallChart hw₁ hw₂ := ⟨i, p, r, hr, hball⟩
  have hp : p ∈ (model B).source := by
    rw [model_source]
    exact Metric.mem_ball_self hr
  have hmem := (model B).map_source hp
  have heq : model B p = x := (regularChart hw₁ hw₂ i).left_inv hx
  exact ⟨B, heq ▸ hmem⟩

def timeDomain {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) : Set ℝ :=
  {t | (model B).symm x + t • v ∈ Metric.ball B.center B.radius}

def curve {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ) : Regular L₁ L₂ w :=
  model B ((model B).symm x + t • v)

theorem curve_eq_physical_curve {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) :
    curve B v x = LocalDirectionalCurves.curve hw₁ hw₂ B.index v x := rfl

theorem timeDomain_open {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) : IsOpen (timeDomain B v x) :=
  Metric.isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))

theorem timeDomain_convex {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) : Convex ℝ (timeDomain B v x) := by
  intro s hs t ht a b ha hb hab
  have h := convex_ball B.center B.radius hs ht ha hb hab
  change (model B).symm x + (a * s + b * t) • v ∈ Metric.ball B.center B.radius
  have heq : a • ((model B).symm x + s • v) + b • ((model B).symm x + t • v) =
      (model B).symm x + (a * s + b * t) • v := by
    calc
      _ = (a + b) • (model B).symm x + (a * s + b * t) • v := by module
      _ = _ := by rw [hab, one_smul]
  rwa [heq] at h

theorem timeDomain_subset_physical {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) :
    timeDomain B v x ⊆ LocalDirectionalCurves.timeDomain hw₁ hw₂ B.index v x :=
  fun _ ht => B.ball_subset ht

theorem zero_mem_timeDomain {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) (hx : x ∈ (model B).target) :
    0 ∈ timeDomain B v x := by
  change (model B).symm x + (0 : ℝ) • v ∈ Metric.ball B.center B.radius
  rw [zero_smul, add_zero]
  exact (model_source B) ▸ (model B).map_target hx

theorem curve_zero {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) (hx : x ∈ (model B).target) :
    curve B v x 0 = x := by
  change model B ((model B).symm x + (0 : ℝ) • v) = x
  rw [zero_smul, add_zero]
  exact (model B).right_inv hx

theorem isMIntegralCurveOn_curve {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve B v x) (FlatVectorField.field hw₁ hw₂ v)
      (timeDomain B v x) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  rw [curve_eq_physical_curve]
  exact (LocalDirectionalIntegralCurves.isMIntegralCurveOn_curve hw₁ hw₂ B.index v x).mono
    (timeDomain_subset_physical B v x)

def timeMap {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ) :
    OpenPartialHomeomorph (Regular L₁ L₂ w) (Regular L₁ L₂ w) :=
  ((model B).symm.transHomeomorph (Homeomorph.addRight (t • v))).trans (model B)

theorem timeMap_apply {L₁ L₂ : Lattice} {w : Plane} {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ) (x : Regular L₁ L₂ w) :
    timeMap B v t x = curve B v x t := rfl

theorem mem_timeMap_source {L₁ L₂ : Lattice} {w : Plane}
    {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}
    (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ) (x : Regular L₁ L₂ w) :
    x ∈ (timeMap B v t).source ↔ x ∈ (model B).target ∧ t ∈ timeDomain B v x := by
  change (x ∈ (model B).target ∧ (model B).symm x + t • v ∈ (model B).source) ↔ _
  rw [model_source]
  rfl

end MNEC.DirectionalBallCharts
