module

public import MNEC.DirectionalMaximalCurves
public import MNEC.MaximalFlowAction

/-!
# The actual directional additive action on complete native orbits

The subset is defined by the proved maximal trajectory domains. The
generic autonomous time-shift theorem is specialized to the actual smooth
physical field. No nonemptiness or conullness of this subset is asserted.
-/

noncomputable section
@[expose] public section

namespace MNEC.DirectionalCompleteAction

open LatticeTorus RegularChartedSpace DirectionalMaximalCurves Set
open scoped Manifold ContDiff Topology

section ActualManifold

variable {L₁ L₂ : Lattice} {w : Plane}
variable (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)

def completeOrbitSet (v : Plane) : Set (Regular L₁ L₂ w) :=
  {x | domain hw₁ hw₂ v x = Set.univ}

abbrev CompleteOrbits (v : Plane) := ↥(completeOrbitSet hw₁ hw₂ v)

theorem complete_time_mem (v : Plane) (x : CompleteOrbits hw₁ hw₂ v) (t : ℝ) :
    t ∈ domain hw₁ hw₂ v x.val := by
  rw [x.property]
  exact Set.mem_univ _

theorem domain_at_time (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ domain hw₁ hw₂ v x) :
    domain hw₁ hw₂ v (trajectory hw₁ hw₂ v x t) = {s | s + t ∈ domain hw₁ hw₂ v x} := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.maximalDomain_at_time (field_contMDiff_one hw₁ hw₂ v) x t ht

theorem trajectory_add (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ domain hw₁ hw₂ v x) (s : ℝ)
    (hs : s ∈ domain hw₁ hw₂ v (trajectory hw₁ hw₂ v x t)) :
    trajectory hw₁ hw₂ v (trajectory hw₁ hw₂ v x t) s = trajectory hw₁ hw₂ v x (s + t) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.maximalCurve_add (field_contMDiff_one hw₁ hw₂ v) x t ht s hs

theorem completeOrbitSet_forward (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ completeOrbitSet hw₁ hw₂ v) (t : ℝ) :
    trajectory hw₁ hw₂ v x t ∈ completeOrbitSet hw₁ hw₂ v := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.completeOrbitSet_forward (field_contMDiff_one hw₁ hw₂ v) x hx t

theorem completeOrbitSet_time_iff (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ domain hw₁ hw₂ v x) :
    trajectory hw₁ hw₂ v x t ∈ completeOrbitSet hw₁ hw₂ v ↔ x ∈ completeOrbitSet hw₁ hw₂ v := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.completeOrbitSet_time_iff (field_contMDiff_one hw₁ hw₂ v) x t ht

@[instance_reducible] def completeAction (v : Plane) : AddAction ℝ (CompleteOrbits hw₁ hw₂ v) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.completeAction (field_contMDiff_one hw₁ hw₂ v)

def timeMap (v : Plane) (t : ℝ) (x : CompleteOrbits hw₁ hw₂ v) : CompleteOrbits hw₁ hw₂ v := by
  let := completeAction hw₁ hw₂ v
  exact t +ᵥ x

theorem timeMap_value (v : Plane) (t : ℝ) (x : CompleteOrbits hw₁ hw₂ v) :
    (timeMap hw₁ hw₂ v t x).val = trajectory hw₁ hw₂ v x.val t := rfl

theorem timeMap_zero (v : Plane) (x : CompleteOrbits hw₁ hw₂ v) : timeMap hw₁ hw₂ v 0 x = x := by
  let := completeAction hw₁ hw₂ v
  exact zero_vadd ℝ x

theorem timeMap_add (v : Plane) (s t : ℝ) (x : CompleteOrbits hw₁ hw₂ v) :
    timeMap hw₁ hw₂ v (s + t) x = timeMap hw₁ hw₂ v s (timeMap hw₁ hw₂ v t x) := by
  let := completeAction hw₁ hw₂ v
  exact add_vadd s t x

theorem timeMap_neg_timeMap (v : Plane) (t : ℝ) (x : CompleteOrbits hw₁ hw₂ v) :
    timeMap hw₁ hw₂ v (-t) (timeMap hw₁ hw₂ v t x) = x := by
  rw [← timeMap_add, neg_add_cancel, timeMap_zero]

def timeEquiv (v : Plane) (t : ℝ) : CompleteOrbits hw₁ hw₂ v ≃ CompleteOrbits hw₁ hw₂ v where
  toFun := timeMap hw₁ hw₂ v t
  invFun := timeMap hw₁ hw₂ v (-t)
  left_inv := timeMap_neg_timeMap hw₁ hw₂ v t
  right_inv x := by simpa only [neg_neg] using timeMap_neg_timeMap hw₁ hw₂ v (-t) x

/-- Every orbit of the constructed action is a global native integral curve. -/
theorem timeMap_isMIntegralCurve (v : Plane) (x : CompleteOrbits hw₁ hw₂ v) :
    letI := chartedSpace hw₁ hw₂
    IsMIntegralCurve (fun t => (timeMap hw₁ hw₂ v t x).val) (FlatVectorField.field hw₁ hw₂ v) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalFlowAction.timeMap_isMIntegralCurve (field_contMDiff_one hw₁ hw₂ v) x

end ActualManifold

end MNEC.DirectionalCompleteAction
