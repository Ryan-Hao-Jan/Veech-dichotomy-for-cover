module

public import MNEC.NativeLocalPrimitives
public import MNEC.NativePartialDirectionalFlow

@[expose] public section
noncomputable section

namespace MNEC.NativePrimitiveTrajectory

open LatticeTorus NativeAbelianDifferential NativePrimitiveTransitions
open NativeRegularTranslationAtlas NativeDirectionalDynamics NativeLocalPrimitives
open Set Filter Topology
open scoped Manifold ContDiff Classical

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

def value (q : Differential X) (v : Plane) (x : Regular q) (F : X → ℂ) (t : ℝ) : Plane :=
  toPlane (F (trajectory q v x t).val)

theorem continuousAt_trajectory (q : Differential X) (v : Plane) (x : Regular q) (s : ℝ)
    (hs : s ∈ domain q v x) : ContinuousAt (trajectory q v x) s := by
  have hc : Continuous (fun t : ℝ => (v, t, x)) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  simpa only [NativePartialDirectionalFlow.jointTrajectory, Function.comp_def] using
    (NativePartialDirectionalFlow.continuousAt_jointTrajectory q (v, s, x) hs).comp
      (f := fun t : ℝ => (v, t, x)) (x := s) hc.continuousAt

/-- Actual local primitive affinity at time zero, derived from the genuine
physical chart and the arbitrary-function constant-difference theorem. -/
theorem zero_affinity_germ (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y)) (hxU : x.val ∈ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ domain q v x ∧
      value q v x F t = toPlane (F x.val) + t • v := by
  let e := primitiveChart q x
  let E := coordinateChart q x
  let c := F x.val - e x.val
  have hd : ∀ᶠ y in 𝓝 x.val, F y = e y + c :=
    NativeLocalPrimitives.difference_germ q e F e.source U e.open_source hU
      (chosen q x).derivative hF x.val ⟨(chosen q x).center, hxU⟩
  have hc : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝 0) (𝓝 x.val) := by
    have hcont := continuous_subtype_val.continuousAt.comp
      (continuousAt_trajectory q v x 0 (zero_mem_domain q v x))
    simpa only [Function.comp_def, trajectory_initial] using hcont.tendsto
  obtain ⟨ε, hε, hstraight⟩ := local_physical_straightness q x v x (coordinateChart_center q x)
  have hdself := hd.self_of_nhds
  filter_upwards [hc hd, Metric.ball_mem_nhds (0 : ℝ) hε] with t hdt ht
  obtain ⟨htD, htE⟩ := hstraight t ht
  refine ⟨htD, ?_⟩
  have hplane := congrArg toPlane hdt
  have hbase := congrArg toPlane hdself
  rw [map_add] at hplane hbase
  have hcoords : toPlane (e (trajectory q v x t).val) = toPlane (e x.val) + t • v := htE
  change toPlane (F (trajectory q v x t).val) = _
  rw [hplane, hcoords, hbase]
  abel

/-- The autonomous native time-shift law transports the derived germ to
every valid time, without assuming complex differentiability of the curve. -/
theorem affinity_germ (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (s : ℝ) (hs : s ∈ domain q v x) (hsU : (trajectory q v x s).val ∈ U) :
    ∀ᶠ t in 𝓝 s, value q v x F t = value q v x F s + (t - s) • v := by
  let y := trajectory q v x s
  have hz := zero_affinity_germ q v y U hU F hF hsU
  have hsub : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t - s) s := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using! hc.tendsto
  filter_upwards [hsub hz] with t ht
  have hshift : trajectory q v y (t - s) = trajectory q v x t :=
    (trajectory_add q v x s hs (t - s) ht.1).trans
      (congrArg (trajectory q v x) (by ring))
  simpa only [value, hshift] using ht.2

/-- Subtracting t*v gives an actual zero real derivative on the time
interval. The vector-valued mean value theorem yields global affinity. -/
theorem affinity_on_open_convex (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I) (hD : I ⊆ domain q v x)
    (hstay : ∀ t ∈ I, (trajectory q v x t).val ∈ U) (s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) :
    value q v x F t = value q v x F s + (t - s) • v := by
  let H : ℝ → Plane := fun u => value q v x F u - u • v
  have hder : ∀ u ∈ I, HasFDerivAt H (0 : ℝ →L[ℝ] Plane) u := by
    intro u hu
    have hg := affinity_germ q v x U hU F hF u (hD hu) (hstay u hu)
    have hconst : H =ᶠ[𝓝 u] fun _ => H u := by
      filter_upwards [hg] with z hz
      dsimp only [H]
      rw [hz, sub_smul]
      abel
    exact (hasFDerivAt_const (H u) u).congr_of_eventuallyEq hconst
  have hval : H t = H s := by
    apply hconvex.is_const_of_fderivWithin_eq_zero
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt) _ ht hs
    intro u hu
    rw [fderivWithin_of_isOpen hI hu]
    exact (hder u hu).fderiv
  change value q v x F t - t • v = value q v x F s - s • v at hval
  rw [sub_smul]
  calc
    value q v x F t = (value q v x F t - t • v) + t • v := by abel
    _ = (value q v x F s - s • v) + t • v := by rw [hval]
    _ = value q v x F s + (t • v - s • v) := by abel

theorem affinity_on_open_connected (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (I : Set ℝ) (hI : IsOpen I) (hconnected : IsPreconnected I) (hD : I ⊆ domain q v x)
    (hstay : ∀ t ∈ I, (trajectory q v x t).val ∈ U) (s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) :
    value q v x F t = value q v x F s + (t - s) • v :=
  affinity_on_open_convex q v x U hU F hF I hI hconnected.ordConnected.convex hD hstay s t hs ht

end MNEC.NativePrimitiveTrajectory

