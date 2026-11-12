module

public import MNEC.NativePartialDirectionalFlow
public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.GDelta.Basic

/-! The actual complete-orbit action and continuous flow for an arbitrary native
holomorphic differential. Completeness defines the phase space; no full-area claim
is used in constructing its maps, topology or native integral curves. -/

@[expose] public section
noncomputable section

namespace MNEC.NativeCompleteDirectionalFlow

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics Set Topology
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : NativeAbelianDifferential.Differential X)
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local notation "R" => Regular q

def completeOrbitSet (v : Plane) : Set R := {x | domain q v x = univ}

abbrev CompleteOrbits (v : Plane) := ↥(completeOrbitSet q v)

theorem complete_time_mem (v : Plane) (x : CompleteOrbits q v) (t : ℝ) :
    t ∈ domain q v x.val := by
  rw [x.property]
  trivial

theorem completeOrbitSet_forward (v : Plane) (x : R)
    (hx : x ∈ completeOrbitSet q v) (t : ℝ) :
    trajectory q v x t ∈ completeOrbitSet q v := by
  change domain q v (trajectory q v x t) = univ
  have ht : t ∈ domain q v x := by rw [hx]; trivial
  rw [domain_at_time q v x t ht]
  change {s | s + t ∈ domain q v x} = univ
  change domain q v x = univ at hx
  simp only [hx, mem_univ, ofPred_true]

theorem completeOrbitSet_time_iff (v : Plane) (x : R) (t : ℝ)
    (ht : t ∈ domain q v x) :
    trajectory q v x t ∈ completeOrbitSet q v ↔
      x ∈ completeOrbitSet q v := by
  constructor
  · intro hy
    change domain q v (trajectory q v x t) = univ at hy
    change domain q v x = univ
    apply Set.eq_univ_of_forall
    intro u
    have hs : u - t ∈ domain q v (trajectory q v x t) := by rw [hy]; trivial
    rw [domain_at_time q v x t ht] at hs
    change (u - t) + t ∈ domain q v x at hs
    simpa only [sub_add_cancel] using hs
  · exact fun hx => completeOrbitSet_forward q v x hx t

def timeMap (v : Plane) (t : ℝ) (x : CompleteOrbits q v) : CompleteOrbits q v :=
  ⟨trajectory q v x.val t, completeOrbitSet_forward q v x.val x.property t⟩

theorem timeMap_value (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    (timeMap q v t x).val = trajectory q v x.val t := rfl

theorem timeMap_zero (v : Plane) (x : CompleteOrbits q v) : timeMap q v 0 x = x := by
  apply Subtype.ext
  exact trajectory_initial q v x.val

theorem timeMap_add (v : Plane) (s t : ℝ) (x : CompleteOrbits q v) :
    timeMap q v (s + t) x = timeMap q v s (timeMap q v t x) := by
  apply Subtype.ext
  exact (trajectory_add q v x.val t (complete_time_mem q v x t) s
    (complete_time_mem q v (timeMap q v t x) s)).symm

@[instance_reducible] def completeAction (v : Plane) : AddAction ℝ (CompleteOrbits q v) where
  vadd := timeMap q v
  zero_vadd := timeMap_zero q v
  add_vadd := timeMap_add q v

theorem timeMap_neg_timeMap (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    timeMap q v (-t) (timeMap q v t x) = x := by
  rw [← timeMap_add, neg_add_cancel, timeMap_zero]

def timeEquiv (v : Plane) (t : ℝ) : CompleteOrbits q v ≃ CompleteOrbits q v where
  toFun := timeMap q v t
  invFun := timeMap q v (-t)
  left_inv := timeMap_neg_timeMap q v t
  right_inv x := by simpa only [neg_neg] using timeMap_neg_timeMap q v (-t) x

theorem completeOrbitSet_eq_iInter (v : Plane) :
    completeOrbitSet q v = ⋂ k : ℕ,
      (NativePartialDirectionalFlow.timeSource q v (k : ℝ) ∩
        NativePartialDirectionalFlow.timeSource q v (-(k : ℝ))) := by
  ext x
  constructor
  · intro hx
    have hD : domain q v x = univ := hx
    apply mem_iInter.mpr
    intro k
    constructor <;> change _ ∈ domain q v x <;> rw [hD] <;> trivial
  · intro hx
    change domain q v x = univ
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨k, hk⟩ := exists_nat_gt |t|
    have hends := mem_iInter.mp hx k
    exact (domain_ordConnected q v x).out hends.2 hends.1
      ⟨(neg_le_neg hk.le).trans (neg_abs_le t), (le_abs_self t).trans hk.le⟩

theorem completeOrbitSet_isGδ (v : Plane) : IsGδ (completeOrbitSet q v) := by
  rw [completeOrbitSet_eq_iInter]
  exact IsGδ.iInter_of_isOpen (fun k =>
    (NativePartialDirectionalFlow.timeSource_open q v (k : ℝ)).inter
      (NativePartialDirectionalFlow.timeSource_open q v (-(k : ℝ))))

theorem completeOrbitSet_measurable (v : Plane) : MeasurableSet (completeOrbitSet q v) := by
  rw [completeOrbitSet_eq_iInter]
  exact MeasurableSet.iInter (fun k =>
    (NativePartialDirectionalFlow.timeSource_open q v (k : ℝ)).measurableSet.inter
      (NativePartialDirectionalFlow.timeSource_open q v (-(k : ℝ))).measurableSet)

theorem continuous_joint_timeMap (v : Plane) :
    Continuous (fun p : ℝ × CompleteOrbits q v => timeMap q v p.1 p.2) := by
  let F : ℝ × CompleteOrbits q v → Plane × ℝ × R := fun p => (v, p.1, p.2.val)
  have hF : Continuous F := continuous_const.prodMk
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hval : Continuous (fun p : ℝ × CompleteOrbits q v =>
      (timeMap q v p.1 p.2).val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : F p ∈ NativePartialDirectionalFlow.valid q := complete_time_mem q v p.2 p.1
    have h := (NativePartialDirectionalFlow.continuousAt_jointTrajectory q (F p) hp).comp hF.continuousAt
    simpa only [timeMap_value, NativePartialDirectionalFlow.jointTrajectory, Function.comp_def, F] using h
  exact hval.subtype_mk _

theorem continuous_timeMap (v : Plane) (t : ℝ) : Continuous (timeMap q v t) :=
  (continuous_joint_timeMap q v).comp (continuous_const.prodMk continuous_id)

theorem measurable_timeMap (v : Plane) (t : ℝ) : Measurable (timeMap q v t) :=
  (continuous_timeMap q v t).measurable

def timeHomeomorph (v : Plane) (t : ℝ) : CompleteOrbits q v ≃ₜ CompleteOrbits q v where
  toEquiv := timeEquiv q v t
  continuous_toFun := continuous_timeMap q v t
  continuous_invFun := continuous_timeMap q v (-t)

def flow (v : Plane) : Flow ℝ (CompleteOrbits q v) where
  toFun := timeMap q v
  cont' := continuous_joint_timeMap q v
  map_add' := timeMap_add q v
  map_zero' := timeMap_zero q v

theorem flow_value (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    (flow q v t x).val = trajectory q v x.val t := rfl

theorem flow_isMIntegralCurve (v : Plane) (x : CompleteOrbits q v) :
    letI := chartedSpace q
    IsMIntegralCurve (I := 𝓘(ℝ, Plane)) (fun t => (flow q v t x).val)
      (field q v) := by
  let := chartedSpace q
  apply isMIntegralCurve_iff_isMIntegralCurveOn.mpr
  have h := trajectory_isMIntegralCurveOn q v x.val
  have hx : domain q v x.val = univ := x.property
  rw [hx] at h
  exact h

end MNEC.NativeCompleteDirectionalFlow



