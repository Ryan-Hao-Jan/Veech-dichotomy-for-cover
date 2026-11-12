module

public import VeechDichotomy.NativePeriodicOrbits

/-! A single actual dense complete native orbit has injective time
parametrization. Minimality of all other orbits is unnecessary: a time
collision makes this orbit periodic, contradicting its proved non-density. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDenseOrbitInjectivity

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

theorem regular_dense (x : CompleteOrbits q v)
    (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val)) :
    DenseRange (fun t : ℝ => (flow q v t x).val) := by
  change Dense (range (fun t : ℝ => (flow q v t x).val))
  rw [Subtype.dense_iff, ← range_comp]
  change regularSet q ⊆ closure (range (fun t : ℝ => (flow q v t x).val.val))
  rw [hdense.closure_range]
  exact subset_univ _

theorem trajectory_injective (hv : v ≠ 0) (x : CompleteOrbits q v)
    (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val)) :
    Function.Injective (trajectory q v x.val) := by
  intro s t hst
  by_contra hne
  have htime : timeMap q v s x = timeMap q v t x := Subtype.ext hst
  have hperiod : timeMap q v (s - t) x = x := by
    calc
      timeMap q v (s - t) x = timeMap q v (-t) (timeMap q v s x) := by rw [← timeMap_add]; congr 1; ring
      _ = timeMap q v (-t) (timeMap q v t x) := congrArg (timeMap q v (-t)) htime
      _ = x := timeMap_neg_timeMap q v t x
  exact NativePeriodicOrbits.periodic_orbit_not_dense q v hv x (sub_ne_zero.mpr hne) hperiod hdense

theorem flow_injective (hv : v ≠ 0) (x : CompleteOrbits q v)
    (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val)) :
    Function.Injective (fun t : ℝ => flow q v t x) := by
  intro s t hst
  exact trajectory_injective q v hv x hdense (congrArg Subtype.val hst)

end VeechDichotomy.NativeDenseOrbitInjectivity
