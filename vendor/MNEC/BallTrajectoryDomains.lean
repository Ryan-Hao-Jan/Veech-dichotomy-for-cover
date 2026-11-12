module

public import MNEC.DirectionalBallCharts
public import MNEC.DirectionalMaximalCurves

@[expose] public section

/-!
# Convex physical ball steps lie on actual maximal native trajectories

The valid times of a ball chart form an open convex interval. Its actual
straight curve is a proved native integral curve with the correct initial
value, so native interval maximality identifies every valid time and point
with the actual maximal trajectory. Convexity also includes the entire
intervening time segment; endpoint membership cannot jump across a slit.
-/

noncomputable section

namespace MNEC.BallTrajectoryDomains

open LatticeTorus RegularChartedSpace DirectionalBallCharts Set
open scoped Manifold Topology

variable {L₁ L₂ : Lattice} {w : Plane}
variable {hw₁ : L₁.EmbeddedSlit w} {hw₂ : L₂.EmbeddedSlit w}

theorem extends_ball_curve (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (model B).target) :
    timeDomain B v x ⊆ DirectionalMaximalCurves.domain hw₁ hw₂ v x ∧
      EqOn (DirectionalMaximalCurves.trajectory hw₁ hw₂ v x) (curve B v x) (timeDomain B v x) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  exact DirectionalMaximalCurves.extends_every_open_interval hw₁ hw₂ v x
    (timeDomain B v x) (curve B v x) (timeDomain_open B v x)
    (timeDomain_convex B v x).ordConnected (zero_mem_timeDomain B v x hx)
    (curve_zero B v x hx) (isMIntegralCurveOn_curve B v x)

theorem timeDomain_subset_domain (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (model B).target) :
    timeDomain B v x ⊆ DirectionalMaximalCurves.domain hw₁ hw₂ v x :=
  (extends_ball_curve B v x hx).1

theorem trajectory_eq_curve (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (model B).target) :
    EqOn (DirectionalMaximalCurves.trajectory hw₁ hw₂ v x) (curve B v x) (timeDomain B v x) :=
  (extends_ball_curve B v x hx).2

theorem curve_mem_chart (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (t : ℝ) (ht : t ∈ timeDomain B v x) : curve B v x t ∈ (model B).target := by
  have hsource : (model B).symm x + t • v ∈ (model B).source := by
    rw [model_source]
    exact ht
  exact (model B).map_source hsource

theorem coordinates_curve (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (t : ℝ) (ht : t ∈ timeDomain B v x) :
    (model B).symm (curve B v x t) = (model B).symm x + t • v := by
  have hsource : (model B).symm x + t • v ∈ (model B).source := by
    rw [model_source]
    exact ht
  exact (model B).left_inv hsource

theorem segment_mem_timeDomain (B : BallChart hw₁ hw₂) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (model B).target) (t : ℝ) (ht : t ∈ timeDomain B v x) :
    uIcc (0 : ℝ) t ⊆ timeDomain B v x :=
  (timeDomain_convex B v x).ordConnected.uIcc_subset (zero_mem_timeDomain B v x hx) ht

theorem trajectory_segment_in_chart (B : BallChart hw₁ hw₂) (v : Plane)
    (x : Regular L₁ L₂ w) (hx : x ∈ (model B).target) (t : ℝ)
    (ht : t ∈ timeDomain B v x) :
    ∀ s ∈ uIcc (0 : ℝ) t, DirectionalMaximalCurves.trajectory hw₁ hw₂ v x s ∈ (model B).target := by
  intro s hs
  have hvalid := segment_mem_timeDomain B v x hx t ht hs
  rw [trajectory_eq_curve B v x hx hvalid]
  exact curve_mem_chart B v x s hvalid

theorem trajectory_segment_coordinates (B : BallChart hw₁ hw₂) (v : Plane)
    (x : Regular L₁ L₂ w) (hx : x ∈ (model B).target) (t : ℝ)
    (ht : t ∈ timeDomain B v x) :
    ∀ s ∈ uIcc (0 : ℝ) t,
      (model B).symm (DirectionalMaximalCurves.trajectory hw₁ hw₂ v x s) =
        (model B).symm x + s • v := by
  intro s hs
  have hvalid := segment_mem_timeDomain B v x hx t ht hs
  rw [trajectory_eq_curve B v x hx hvalid]
  exact coordinates_curve B v x s hvalid

/-- A partial ball time map is the actual native maximal trajectory at
that time, and its time belongs to the actual maximal domain. -/
theorem timeMap_time_mem_domain (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ)
    (x : Regular L₁ L₂ w) (hx : x ∈ (timeMap B v t).source) :
    t ∈ DirectionalMaximalCurves.domain hw₁ hw₂ v x := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  exact timeDomain_subset_domain B v x hxB ht

theorem timeMap_eq_trajectory (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ)
    (x : Regular L₁ L₂ w) (hx : x ∈ (timeMap B v t).source) :
    timeMap B v t x = DirectionalMaximalCurves.trajectory hw₁ hw₂ v x t := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  rw [timeMap_apply]
  exact (trajectory_eq_curve B v x hxB ht).symm

/-- All intermediate native trajectory points of an accepted ball step
remain in that one actual chart, including steps of negative duration. -/
theorem timeMap_segment_in_chart (B : BallChart hw₁ hw₂) (v : Plane) (t : ℝ)
    (x : Regular L₁ L₂ w) (hx : x ∈ (timeMap B v t).source) :
    ∀ s ∈ uIcc (0 : ℝ) t,
      s ∈ DirectionalMaximalCurves.domain hw₁ hw₂ v x ∧
        DirectionalMaximalCurves.trajectory hw₁ hw₂ v x s ∈ (model B).target := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  intro s hs
  exact ⟨timeDomain_subset_domain B v x hxB (segment_mem_timeDomain B v x hxB t ht hs),
    trajectory_segment_in_chart B v x hxB t ht s hs⟩

end MNEC.BallTrajectoryDomains
