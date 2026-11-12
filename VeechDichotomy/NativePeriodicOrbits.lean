module

public import VeechDichotomy.NativeDynamics
public import MNEC.NativePrimitiveTrajectory
public import Mathlib.Algebra.Field.Periodic

/-! Actual nonsingular directional orbits have flat area zero. A
periodic orbit is compact and therefore cannot be dense in the surface.
These are geometric consequences of the constructed translation charts.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePeriodicOrbits

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open MNEC.NativePrimitiveTransitions MNEC.NativeRegularArea MNEC.NativePrimitiveLineNull
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def regularOrbit (q : Differential X) (v : Plane) (x : CompleteOrbits q v) : ℝ → Regular q :=
  fun t => (flow q v t x).val

def surfaceOrbit (q : Differential X) (v : Plane) (x : CompleteOrbits q v) : ℝ → X :=
  fun t => (flow q v t x).val.val

theorem continuous_regularOrbit (q : Differential X) (v : Plane) (x : CompleteOrbits q v) :
    Continuous (regularOrbit q v x) :=
  continuous_subtype_val.comp
    ((continuous_joint_timeMap q v).comp (continuous_id.prodMk continuous_const))

theorem continuous_surfaceOrbit (q : Differential X) (v : Plane) (x : CompleteOrbits q v) :
    Continuous (surfaceOrbit q v x) :=
  continuous_subtype_val.comp (continuous_regularOrbit q v x)

theorem orbit_locally_in_null_set (q : Differential X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) (t : ℝ) :
    ∃ A : Set (Regular q), regularArea q A = 0 ∧
      ∀ᶠ s in 𝓝 t, regularOrbit q v x s ∈ A := by
  let y := regularOrbit q v x t
  let e := primitiveChart q y
  let a := toPlane (e y.val)
  let A := linePreimage q e.source e a v
  have hnull : regularArea q A = 0 :=
    linePreimage_null q e.source e.open_source e (chosen q y).derivative a v hv
  have hstraight := MNEC.NativePrimitiveTrajectory.affinity_germ q v x.val
    e.source e.open_source e (chosen q y).derivative t
    (complete_time_mem q v x t) (chosen q y).center
  have hstay := (continuous_surfaceOrbit q v x).continuousAt
    (e.open_source.mem_nhds (chosen q y).center)
  refine ⟨A, hnull, ?_⟩
  filter_upwards [hstraight, hstay] with s hs hsrc
  refine ⟨hsrc, ?_⟩
  change toPlane (e (trajectory q v x.val s).val) ∈ affineLine a v
  change MNEC.NativePrimitiveTrajectory.value q v x.val e s ∈ affineLine a v
  rw [hs]
  change (a.1 + (s - t) * v.1 - a.1) * v.2 -
    (a.2 + (s - t) * v.2 - a.2) * v.1 = 0
  ring

theorem regularOrbit_area_zero (q : Differential X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) : regularArea q (range (regularOrbit q v x)) = 0 := by
  choose A hnull hnear using orbit_locally_in_null_set q v hv x
  have hnbhd : ∀ t : ℝ, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, regularOrbit q v x s ∈ A t := by
    intro t
    obtain ⟨U, hsub, hU, ht⟩ := mem_nhds_iff.mp (hnear t)
    exact ⟨U, hU, ht, hsub⟩
  choose U hU htU hUA using hnbhd
  have hcover : (univ : Set ℝ) ⊆ ⋃ t : ℝ, U t :=
    fun t _ => mem_iUnion.mpr ⟨t, htU t⟩
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof (univ : Set ℝ)).indexed_countable_subcover
    U hU hcover
  apply measure_mono_null (t := ⋃ n : ℕ, A (f n)) ?_
    (measure_iUnion_null (fun n => hnull (f n)))
  rintro z ⟨t, rfl⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hf (mem_univ t))
  exact mem_iUnion.mpr ⟨n, hUA (f n) t hn⟩

theorem surfaceOrbit_not_surjective (q : Differential X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) : ¬ Function.Surjective (surfaceOrbit q v x) := by
  intro hsurj
  have hreg : Function.Surjective (regularOrbit q v x) := by
    intro z
    obtain ⟨t, ht⟩ := hsurj z.val
    exact ⟨t, Subtype.ext ht⟩
  have hzero := regularOrbit_area_zero q v hv x
  rw [Set.range_eq_univ.mpr hreg] at hzero
  exact (MNEC.NativeFiniteRegularArea.regularArea_univ_pos q).ne' hzero

theorem isCompact_periodic_surfaceOrbit (q : Differential X) (v : Plane)
    (x : CompleteOrbits q v) {T : ℝ} (hT : T ≠ 0) (hperiod : timeMap q v T x = x) :
    IsCompact (range (surfaceOrbit q v x)) := by
  have hp : Function.Periodic (surfaceOrbit q v x) T := by
    intro t
    change (timeMap q v (t + T) x).val.val = (timeMap q v t x).val.val
    rw [timeMap_add, hperiod]
  rw [← hp.image_uIcc hT 0]
  exact isCompact_uIcc.image (continuous_surfaceOrbit q v x)

theorem periodic_orbit_not_dense (q : Differential X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) {T : ℝ} (hT : T ≠ 0) (hperiod : timeMap q v T x = x) :
    ¬ DenseRange (surfaceOrbit q v x) := by
  intro hdense
  apply surfaceOrbit_not_surjective q v hv x
  apply Set.range_eq_univ.mp
  rw [← (isCompact_periodic_surfaceOrbit q v x hT hperiod).isClosed.closure_eq]
  exact hdense.closure_range

/-- The precise periodic-orbit alternative needed when using Veech's
topological dichotomy; no cylinder decomposition is assumed here. -/
def AllCompleteOrbitsPeriodic (q : Differential X) (v : Plane) : Prop :=
  ∀ x : CompleteOrbits q v, ∃ T : ℝ, T ≠ 0 ∧ timeMap q v T x = x

theorem not_allPeriodic_of_dense_orbit (q : Differential X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) (hx : DenseRange (surfaceOrbit q v x)) :
    ¬ AllCompleteOrbitsPeriodic q v := by
  intro hall
  obtain ⟨T, hT, hperiod⟩ := hall x
  exact periodic_orbit_not_dense q v hv x hT hperiod hx

end VeechDichotomy.NativePeriodicOrbits
