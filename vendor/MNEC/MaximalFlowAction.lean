module

public import MNEC.MaximalIntegralCurve
public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section

/-!
# Native maximal-curve time shifts and the complete-orbit additive action

Autonomy and the proved maximal restriction property determine exactly
how maximal domains and curves change under time translation. These laws
give an actual additive action of `ℝ` on the subtype of points whose
maximal trajectories are defined for all times.

The complete-orbit subtype is defined from the proved native trajectories.
No nonemptiness, conullness, completeness of every trajectory, action law,
or time-shift law is assumed.
-/

noncomputable section

namespace MNEC.MaximalFlowAction

open MaximalIntegralCurve Set Filter Function
open scoped Manifold Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def shiftedDomain (v : (x : M) → TangentSpace I x) (x : M) (t : ℝ) : Set ℝ :=
  {s | s + t ∈ maximalDomain v x}

theorem shiftedDomain_open (v : (x : M) → TangentSpace I x) (x : M) (t : ℝ) :
    IsOpen (shiftedDomain v x t) :=
  (maximalDomain_open v x).preimage (continuous_id.add_const t)

theorem shiftedDomain_ordConnected (v : (x : M) → TangentSpace I x) (x : M) (t : ℝ) :
    OrdConnected (shiftedDomain v x t) :=
  (maximalDomain_ordConnected v x).preimage_mono (monotone_id.add_const t)

def completeOrbitSet (v : (x : M) → TangentSpace I x) : Set M :=
  {x | maximalDomain v x = univ}

abbrev CompleteOrbits (v : (x : M) → TangentSpace I x) := ↥(completeOrbitSet v)

theorem complete_time_mem {v : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ completeOrbitSet v) (t : ℝ) : t ∈ maximalDomain v x := by
  change maximalDomain v x = univ at hx
  rw [hx]
  exact Set.mem_univ _

section ShiftRestriction

variable [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- The original maximal trajectory, shifted to a point on it, is a
restriction of the newly based maximal trajectory. -/
theorem shifted_solution_extends
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) (ht : t ∈ maximalDomain v x) :
    shiftedDomain v x t ⊆ maximalDomain v (maximalCurve v x t) ∧
      EqOn (maximalCurve v (maximalCurve v x t))
        (fun s => maximalCurve v x (s + t)) (shiftedDomain v x t) := by
  apply extends_every_open_interval hv (shiftedDomain v x t)
    (fun s => maximalCurve v x (s + t))
    (shiftedDomain_open v x t) (shiftedDomain_ordConnected v x t)
  · change 0 + t ∈ maximalDomain v x
    simpa only [zero_add] using ht
  · simp only [zero_add]
  · exact (maximalCurve_isMIntegralCurveOn (x₀ := x) hv).comp_add t

end ShiftRestriction

section AutonomousAction

variable [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- The reverse time lies in the newly based maximal domain and returns
to the original initial point. -/
theorem reverse_time
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) (ht : t ∈ maximalDomain v x) :
    -t ∈ maximalDomain v (maximalCurve v x t) ∧
      maximalCurve v (maximalCurve v x t) (-t) = x := by
  obtain ⟨hsub, heq⟩ := shifted_solution_extends hv x t ht
  have hneg : -t ∈ shiftedDomain v x t := by
    change -t + t ∈ maximalDomain v x
    simpa only [neg_add_cancel] using (zero_mem_maximalDomain (x₀ := x) hv)
  refine ⟨hsub hneg, ?_⟩
  have h := heq hneg
  change maximalCurve v (maximalCurve v x t) (-t) = maximalCurve v x (-t + t) at h
  rw [neg_add_cancel, maximalCurve_initial hv] at h
  exact h

/-- The actual maximal domain at time `t` is exactly the translated
original maximal domain. The reverse inclusion is proved by shifting back. -/
theorem maximalDomain_at_time
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) (ht : t ∈ maximalDomain v x) :
    maximalDomain v (maximalCurve v x t) = shiftedDomain v x t := by
  obtain ⟨hforward, _⟩ := shifted_solution_extends hv x t ht
  obtain ⟨hneg, hreturn⟩ := reverse_time hv x t ht
  have hback := (shifted_solution_extends hv (maximalCurve v x t) (-t) hneg).1
  apply Set.Subset.antisymm
  · intro s hs
    change s + t ∈ maximalDomain v x
    have hshift : s + t ∈ shiftedDomain v (maximalCurve v x t) (-t) := by
      change (s + t) + -t ∈ maximalDomain v (maximalCurve v x t)
      simpa only [add_neg_cancel_right] using hs
    have h := hback hshift
    rw [hreturn] at h
    exact h
  · exact hforward

/-- Native autonomous trajectory composition on the precise maximal
domains. This is a proved time-shift law, not an action axiom. -/
theorem maximalCurve_add
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) (ht : t ∈ maximalDomain v x) (s : ℝ)
    (hs : s ∈ maximalDomain v (maximalCurve v x t)) :
    maximalCurve v (maximalCurve v x t) s = maximalCurve v x (s + t) := by
  have hs' : s ∈ shiftedDomain v x t := by
    rw [← maximalDomain_at_time hv x t ht]
    exact hs
  exact (shifted_solution_extends hv x t ht).2 hs'

theorem completeOrbitSet_forward
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (hx : x ∈ completeOrbitSet v) (t : ℝ) :
    maximalCurve v x t ∈ completeOrbitSet v := by
  change maximalDomain v (maximalCurve v x t) = univ
  rw [maximalDomain_at_time hv x t (complete_time_mem hx t)]
  change {s | s + t ∈ maximalDomain v x} = univ
  change maximalDomain v x = univ at hx
  simp only [hx, mem_univ, ofPred_true]

/-- Completeness is invariant along every defined native trajectory. -/
theorem completeOrbitSet_time_iff
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) (ht : t ∈ maximalDomain v x) :
    maximalCurve v x t ∈ completeOrbitSet v ↔ x ∈ completeOrbitSet v := by
  constructor
  · intro hy
    change maximalDomain v (maximalCurve v x t) = univ at hy
    change maximalDomain v x = univ
    apply Set.eq_univ_of_forall
    intro u
    have hs : u - t ∈ maximalDomain v (maximalCurve v x t) := by rw [hy]; trivial
    rw [maximalDomain_at_time hv x t ht] at hs
    change (u - t) + t ∈ maximalDomain v x at hs
    simpa only [sub_add_cancel] using hs
  · exact fun hx => completeOrbitSet_forward hv x hx t

def timeMap
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (t : ℝ) (x : CompleteOrbits v) : CompleteOrbits v :=
  ⟨maximalCurve v x.val t, completeOrbitSet_forward hv x.val x.property t⟩

theorem timeMap_zero
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : CompleteOrbits v) : timeMap hv 0 x = x := by
  apply Subtype.ext
  exact maximalCurve_initial hv

theorem timeMap_add
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (s t : ℝ) (x : CompleteOrbits v) : timeMap hv (s + t) x = timeMap hv s (timeMap hv t x) := by
  apply Subtype.ext
  change maximalCurve v x.val (s + t) = maximalCurve v (maximalCurve v x.val t) s
  exact (maximalCurve_add hv x.val t (complete_time_mem x.property t) s
    (complete_time_mem (completeOrbitSet_forward hv x.val x.property t) s)).symm

/-- An actual additive real action on exactly the complete native orbits.
The subtype may be empty; no measure or full-completeness statement is included. -/
@[instance_reducible] def completeAction
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    AddAction ℝ (CompleteOrbits v) where
  vadd := timeMap hv
  zero_vadd := timeMap_zero hv
  add_vadd := timeMap_add hv

/-- Projected action trajectories are genuine global native integral
curves of the original vector field. -/
theorem timeMap_isMIntegralCurve
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : CompleteOrbits v) : IsMIntegralCurve (fun t => (timeMap hv t x).val) v := by
  change IsMIntegralCurve (maximalCurve v x.val) v
  apply isMIntegralCurve_iff_isMIntegralCurveOn.mpr
  have h := maximalCurve_isMIntegralCurveOn (x₀ := x.val) hv
  have hx : maximalDomain v x.val = univ := x.property
  rw [hx] at h
  exact h

end AutonomousAction

end MNEC.MaximalFlowAction
