module

public import VeechDichotomy.NativeTranslationCover
public import VeechDichotomy.NativeDynamics
public import MNEC.TranslationFlowConjugacy
public import VeechDichotomy.FiniteFiberPeriodicity
public import VeechDichotomy.NativePeriodicOrbits

/-! A genuine finite translation cover maps actual complete directional
trajectories to actual complete trajectories with the same time parameter.
The physical identity derivative is proved from the pullback of forms.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverFlow

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover Set Filter Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

local instance : ChartedSpace Plane (Regular ωX) := chartedSpace ωX
local instance : ChartedSpace Plane (Regular ωY) := chartedSpace ωY
local instance : HasGroupoid (Regular ωX) MNEC.TranslationGroupoid.groupoid :=
  has_translation_groupoid ωX
local instance : HasGroupoid (Regular ωY) MNEC.TranslationGroupoid.groupoid :=
  has_translation_groupoid ωY
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular ωX) := isManifold ωX ∞
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular ωY) := isManifold ωY ∞

theorem translation_factor_germ (π : Cover ωX ωY) (y : Regular ωY) :
    ∃ a : Plane,
      coordinateChart ωY y y + a ∈ (coordinateChart ωX (regularMap π y)).target ∧
      ∀ᶠ z in 𝓝 y, regularMap π z =
        (coordinateChart ωX (regularMap π y)).symm (coordinateChart ωY y z + a) := by
  let A := coordinateChart ωY y
  let B := coordinateChart ωX (regularMap π y)
  let a := toPlane
    (primitiveChart ωX (regularMap π y) (π.map y.val) - primitiveChart ωY y y.val)
  have hcoord : ∀ᶠ z in 𝓝 y, B (regularMap π z) = A z + a := by
    have h := (continuous_subtype_val : Continuous (Subtype.val : Regular ωY → Y)).continuousAt
      (local_translation π y)
    filter_upwards [h] with z hz
    simpa only [A, B, a, coordinateChart_apply, regularMap, map_add] using congrArg toPlane hz
  have hB : regularMap π y ∈ B.source := coordinateChart_center ωX _
  refine ⟨a, ?_, ?_⟩
  · rw [← hcoord.self_of_nhds]
    exact B.map_source hB
  · filter_upwards [hcoord,
      (continuous_regularMap π).continuousAt (B.open_source.mem_nhds hB)] with z hz hzs
    calc
      regularMap π z = B.symm (B (regularMap π z)) := (B.left_inv hzs).symm
      _ = _ := by rw [hz]

theorem hasMFDerivAt_regularMap (π : Cover ωX ωY) (y : Regular ωY) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularMap π) y
      (ContinuousLinearMap.id ℝ Plane) := by
  obtain ⟨a, htarget, hfactor⟩ := translation_factor_germ π y
  let A := coordinateChart ωY y
  let B := coordinateChart ωX (regularMap π y)
  have he : A ∈ atlas Plane (Regular ωY) := ⟨y, rfl⟩
  have hd : B ∈ atlas Plane (Regular ωX) := ⟨regularMap π y, rfl⟩
  have hi := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) he
    (coordinateChart_center ωY y)).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_id A he y (coordinateChart_center ωY y)] at hi
  have ht : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (fun p : Plane => p + a)
      (A y) (ContinuousLinearMap.id ℝ Plane) := ((hasFDerivAt_id _).add_const a).hasMFDerivAt
  have hj := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) hd htarget).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_symm_id B hd _ htarget] at hj
  have hcomp := hj.comp y (ht.comp y hi)
  simpa only [ContinuousLinearMap.id_comp] using! hcomp.congr_of_eventuallyEq_abuse hfactor

theorem domain_subset (π : Cover ωX ωY) (v : Plane) (y : Regular ωY) :
    domain ωY v y ⊆ domain ωX v (regularMap π y) :=
  (MNEC.TranslationFlowConjugacy.mapped_domain_subset_and_trajectory
    (regularMap π) (hasMFDerivAt_regularMap π) v y).1

theorem trajectory_semiconjugacy (π : Cover ωX ωY) (v : Plane)
    (y : Regular ωY) (t : ℝ) (ht : t ∈ domain ωY v y) :
    regularMap π (trajectory ωY v y t) = trajectory ωX v (regularMap π y) t :=
  MNEC.TranslationFlowConjugacy.trajectory_conjugacy
    (regularMap π) (hasMFDerivAt_regularMap π) v y t ht

theorem complete_maps_to_complete (π : Cover ωX ωY) (v : Plane)
    (y : CompleteOrbits ωY v) : regularMap π y.val ∈ completeOrbitSet ωX v := by
  apply Set.eq_univ_of_forall
  intro t
  exact domain_subset π v y.val (complete_time_mem ωY v y t)

def completeMap (π : Cover ωX ωY) (v : Plane) : CompleteOrbits ωY v → CompleteOrbits ωX v :=
  fun y => ⟨regularMap π y.val, complete_maps_to_complete π v y⟩

theorem continuous_completeMap (π : Cover ωX ωY) (v : Plane) :
    Continuous (completeMap π v) :=
  ((continuous_regularMap π).comp continuous_subtype_val).subtype_mk _

theorem flow_semiconjugacy (π : Cover ωX ωY) (v : Plane) (t : ℝ)
    (y : CompleteOrbits ωY v) :
    completeMap π v (flow ωY v t y) = flow ωX v t (completeMap π v y) := by
  apply Subtype.ext
  exact trajectory_semiconjugacy π v y.val t (complete_time_mem ωY v y t)

/-- A complete orbit dense upstairs projects to a complete orbit dense
on the original base curve. No lift of a base affine automorphism is used. -/
theorem projected_orbit_dense (π : Cover ωX ωY) (v : Plane)
    (y : CompleteOrbits ωY v)
    (hy : DenseRange (fun t : ℝ => (flow ωY v t y).val.val)) :
    DenseRange (fun t : ℝ => (flow ωX v t (completeMap π v y)).val.val) := by
  have h := π.surjective.denseRange.comp hy π.holomorphic.continuous
  change DenseRange (fun t : ℝ => π.map (flow ωY v t y).val.val) at h
  convert h using 1
  funext t
  exact (congrArg (fun z : CompleteOrbits ωX v => z.val.val)
    (flow_semiconjugacy π v t y)).symm

theorem minimal_cover_orbit_projects_dense (π : Cover ωX ωY) (v : Plane)
    (hmin : NativeDynamics.MinimalDirection ωY v) (y : CompleteOrbits ωY v) :
    DenseRange (fun t : ℝ => (flow ωX v t (completeMap π v y)).val.val) :=
  projected_orbit_dense π v y (hmin.2 y)

theorem exists_dense_base_orbit_of_minimal_cover (π : Cover ωX ωY) (v : Plane)
    (hmin : NativeDynamics.MinimalDirection ωY v) :
    ∃ x : CompleteOrbits ωX v,
      DenseRange (fun t : ℝ => (flow ωX v t x).val.val) := by
  obtain ⟨y⟩ := NativeDynamics.completeOrbits_nonempty ωY v hmin.1
  exact ⟨completeMap π v y, minimal_cover_orbit_projects_dense π v hmin y⟩

/-- The periodic alternative downstairs is impossible for a direction
minimal upstairs. Turning this into base minimality still requires the
Veech topological dichotomy, which is not assumed in this theorem. -/
theorem base_not_allPeriodic_of_minimal_cover (π : Cover ωX ωY) (v : Plane)
    (hmin : NativeDynamics.MinimalDirection ωY v) :
    ¬ NativePeriodicOrbits.AllCompleteOrbitsPeriodic ωX v := by
  obtain ⟨x, hx⟩ := exists_dense_base_orbit_of_minimal_cover π v hmin
  exact NativePeriodicOrbits.not_allPeriodic_of_dense_orbit ωX v hmin.1 x hx

theorem finite_complete_fibers (π : Cover ωX ωY) (v : Plane)
    (x : CompleteOrbits ωX v) : (completeMap π v ⁻¹' {x}).Finite := by
  let value : CompleteOrbits ωY v → Y := fun z => z.val.val
  have hinj : Function.Injective value := fun z w h => Subtype.ext (Subtype.ext h)
  apply (π.finite_fibers x.val.val).of_injOn (f := value) ?_ hinj.injOn
  intro y hy
  change π.map y.val.val = x.val.val
  exact congrArg (fun z : CompleteOrbits ωX v => z.val.val) hy

/-- The paper's finite-monodromy argument, now for the actual native
time maps and the actual holomorphic translation cover. -/
theorem periodic_base_timeMap_has_periodic_lift (π : Cover ωX ωY) (v : Plane)
    (y : CompleteOrbits ωY v) (T : ℝ)
    (hy : timeMap ωX v T (completeMap π v y) = completeMap π v y) :
    ∃ k : ℕ, 0 < k ∧ Function.IsPeriodicPt (timeMap ωY v T) k y := by
  apply periodic_lift_of_finite_fiber
    (timeEquiv ωY v T).injective
    (fun z => flow_semiconjugacy π v T z)
    (finite_complete_fibers π v (completeMap π v y)) (n := 1) (by decide)
  exact hy

end VeechDichotomy.NativeCoverFlow
