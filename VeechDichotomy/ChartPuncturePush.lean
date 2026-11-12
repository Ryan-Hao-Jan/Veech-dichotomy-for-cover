module

public import VeechDichotomy.RadialPuncturePush
public import VeechDichotomy.FinitePunctureNeighborhoods
public import Mathlib.Topology.Separation.Regular

/-! A local puncture disk supplies a constructed homotopy of the actual
punctured surface. It is the radial homotopy in that chart and the identity
off its compact support. Continuity and avoidance of all removed points
are proved from the displayed chart conditions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ChartPuncturePush

set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Metric unitInterval FinitePunctureNeighborhoods
open scoped Classical

variable {X : Type*} [TopologicalSpace X]

structure Disk (S : Set X) where
  center : X
  center_mem : center ∈ S
  chart : OpenPartialHomeomorph X ℂ
  center_source : center ∈ chart.source
  chart_center : chart center = 0
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  closedBall_target : closedBall 0 radius ⊆ chart.target
  avoids : ∀ z ∈ closedBall 0 radius, z ≠ 0 → chart.symm z ∉ S

namespace Disk

variable {S : Set X} (D : Disk S)

theorem coordinate_ne_zero (x : outside S) (hx : x.val ∈ D.chart.source) : D.chart x.val ≠ 0 := by
  intro hz
  have heq : x.val = D.center := D.chart.injOn hx D.center_source (hz.trans D.chart_center.symm)
  exact x.property (heq.symm ▸ D.center_mem)

def value (t : I) (x : outside S) : X :=
  if x.val ∈ D.chart.source then
    D.chart.symm (RadialPuncturePush.formula D.radius t (D.chart x.val))
  else x.val

theorem formula_target (t : I) (x : outside S) (hx : x.val ∈ D.chart.source) :
    RadialPuncturePush.formula D.radius t (D.chart x.val) ∈ D.chart.target :=
  RadialPuncturePush.formula_mem_of_closedBall_subset D.radius_nonneg t D.closedBall_target
    (D.chart.map_source hx) (D.coordinate_ne_zero x hx)

theorem value_outside (t : I) (x : outside S) : D.value t x ∉ S := by
  by_cases hx : x.val ∈ D.chart.source
  · rw [value, ite_eq_left hx]
    by_cases hn : D.radius ≤ ‖D.chart x.val‖
    · rw [RadialPuncturePush.formula_fixed_of_norm_ge D.radius_nonneg t (D.coordinate_ne_zero x hx) hn,
        D.chart.left_inv hx]
      exact x.property
    · have hnorm : ‖D.chart x.val‖ ≤ D.radius := (lt_of_not_ge hn).le
      let z : RadialPuncturePush.Punctured := ⟨D.chart x.val, D.coordinate_ne_zero x hx⟩
      have hball : RadialPuncturePush.formula D.radius t (D.chart x.val) ∈ closedBall 0 D.radius := by
        have h := RadialPuncturePush.norm_push_le D.radius_nonneg le_rfl t z hnorm
        change ‖RadialPuncturePush.formula D.radius t (D.chart x.val)‖ ≤ D.radius at h
        simpa only [mem_closedBall, dist_zero_right] using h
      exact D.avoids _ hball (RadialPuncturePush.push D.radius t z).property
  · rw [value, ite_eq_right hx]
    exact x.property

def push (t : I) (x : outside S) : outside S := ⟨D.value t x, D.value_outside t x⟩

def support : Set X := D.chart.symm '' closedBall 0 D.radius

theorem support_subset_source : D.support ⊆ D.chart.source := by
  rintro _ ⟨z, hz, rfl⟩
  exact D.chart.map_target (D.closedBall_target hz)

theorem support_compact : IsCompact D.support :=
  (isCompact_closedBall (0 : ℂ) D.radius).image_of_continuousOn
    (D.chart.symm.continuousOn.mono D.closedBall_target)

theorem push_fixed_of_not_support (t : I) (x : outside S) (hx : x.val ∉ D.support) : D.push t x = x := by
  apply Subtype.ext
  change D.value t x = x.val
  by_cases hs : x.val ∈ D.chart.source
  · have hn : D.radius ≤ ‖D.chart x.val‖ := by
      by_contra hn
      apply hx
      refine ⟨D.chart x.val, ?_, D.chart.left_inv hs⟩
      simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hn).le
    rw [value, ite_eq_left hs, RadialPuncturePush.formula_fixed_of_norm_ge D.radius_nonneg t
      (D.coordinate_ne_zero x hs) hn, D.chart.left_inv hs]
  · rw [value, ite_eq_right hs]

theorem push_zero (x : outside S) : D.push 0 x = x := by
  apply Subtype.ext
  change D.value 0 x = x.val
  by_cases hx : x.val ∈ D.chart.source
  · have hz : RadialPuncturePush.formula D.radius 0 (D.chart x.val) = D.chart x.val :=
      congrArg Subtype.val (RadialPuncturePush.push_zero D.radius ⟨_, D.coordinate_ne_zero x hx⟩)
    rw [value, ite_eq_left hx, hz, D.chart.left_inv hx]
  · rw [value, ite_eq_right hx]

theorem continuous_value [T2Space X] : Continuous (fun p : I × outside S => D.value p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hval : Continuous (fun q : I × outside S => q.2.val) := continuous_subtype_val.comp continuous_snd
  by_cases hx : p.2.val ∈ D.chart.source
  · have hcoord : ContinuousAt (fun q : I × outside S => D.chart q.2.val) p :=
      ContinuousAt.comp (f := fun q : I × outside S => q.2.val)
        (D.chart.continuousAt hx) (hval.continuousAt (x := p))
    have hraw : ContinuousAt (fun q : I × outside S =>
        RadialPuncturePush.formula D.radius q.1 (D.chart q.2.val)) p :=
      ContinuousAt.comp (f := fun q : I × outside S => (q.1, D.chart q.2.val))
        (RadialPuncturePush.continuousAt_formula D.radius p.1 (D.coordinate_ne_zero p.2 hx))
        ((continuousAt_fst : ContinuousAt (Prod.fst : I × outside S → I) p).prodMk hcoord)
    have hlocal : ContinuousAt (fun q : I × outside S => D.chart.symm
        (RadialPuncturePush.formula D.radius q.1 (D.chart q.2.val))) p :=
      ContinuousAt.comp (f := fun q : I × outside S =>
        RadialPuncturePush.formula D.radius q.1 (D.chart q.2.val))
        (D.chart.symm.continuousAt (D.formula_target p.1 p.2 hx)) hraw
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [hval.continuousAt (D.chart.open_source.mem_nhds hx)] with q hq
    change q.2.val ∈ D.chart.source at hq
    rw [value, ite_eq_left hq]
  · have hnot : p.2.val ∉ D.support := fun h => hx (D.support_subset_source h)
    have hnear : ∀ᶠ q : I × outside S in 𝓝 p, q.2.val ∉ D.support :=
      hval.continuousAt (D.support_compact.isClosed.isOpen_compl.mem_nhds hnot)
    apply hval.continuousAt.congr_of_eventuallyEq
    filter_upwards [hnear] with q hq
    exact congrArg Subtype.val (D.push_fixed_of_not_support q.1 q.2 hq)

theorem continuous_push [T2Space X] : Continuous (fun p : I × outside S => D.push p.1 p.2) :=
  D.continuous_value.subtype_mk _

def endpoint [T2Space X] : C(outside S, outside S) :=
  ⟨D.push 1, D.continuous_push.comp (continuous_const.prodMk continuous_id)⟩

def homotopy [T2Space X] : (ContinuousMap.id (outside S)).Homotopy D.endpoint where
  toContinuousMap := ⟨fun p => D.push p.1 p.2, D.continuous_push⟩
  map_zero_left := D.push_zero
  map_one_left _ := rfl

theorem endpoint_outside_inner (x : outside S) : (D.push 1 x).val ∉ D.chart.symm '' ball 0 D.radius := by
  rintro ⟨z, hz, hzeq⟩
  have hzT : z ∈ D.chart.target := D.closedBall_target (ball_subset_closedBall hz)
  by_cases hx : x.val ∈ D.chart.source
  · have heq := congrArg D.chart hzeq
    change D.chart (D.chart.symm z) = D.chart (D.value 1 x) at heq
    rw [D.chart.right_inv hzT, value, ite_eq_left hx, D.chart.right_inv (D.formula_target 1 x hx)] at heq
    have hn : D.radius ≤ ‖RadialPuncturePush.formula D.radius 1 (D.chart x.val)‖ :=
      RadialPuncturePush.norm_push_one_ge D.radius ⟨_, D.coordinate_ne_zero x hx⟩
    have hzNorm : ‖z‖ < D.radius := by simpa only [mem_ball, dist_zero_right] using hz
    rw [← heq] at hn
    exact (not_lt_of_ge hn) hzNorm
  · change D.chart.symm z = D.value 1 x at hzeq
    rw [value, ite_eq_right hx] at hzeq
    exact hx (hzeq ▸ D.chart.map_target hzT)

end Disk
end VeechDichotomy.ChartPuncturePush
