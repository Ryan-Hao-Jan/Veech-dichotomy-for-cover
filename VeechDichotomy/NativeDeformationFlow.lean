module

public import VeechDichotomy.NativeDeformationRegular
public import VeechDichotomy.NativeDynamics
public import MNEC.TranslationLinearFlowConjugacy

/-! Exact native directional-flow conjugacy for the constructed compact
SL2 deformation: velocity v is sent to A v with the SAME time parameter.
Maximal domains, complete phases, and minimality are derived from the
proved physical derivative and native ODE uniqueness/maximality.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeDeformationFlow

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeDeformationRegular LinearGroup LinearEquivalences WholeDeformedAtlas
open Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance : ChartedSpace Plane (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid :=
  MNEC.NativeRegularTranslationAtlas.has_translation_groupoid q
local instance : HasGroupoid (Regular (transformed q A)) MNEC.TranslationGroupoid.groupoid :=
  MNEC.NativeRegularTranslationAtlas.has_translation_groupoid (transformed q A)
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := MNEC.NativeRegularTranslationAtlas.isManifold q ∞
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.isManifold (transformed q A) ∞

theorem domain_eq (v : Plane) (x : Regular q) :
    domain q v x = domain (transformed q A) (planeEquiv A v) (regularHomeomorph q A x) :=
  MNEC.TranslationLinearFlowConjugacy.domain_eq (regularHomeomorph q A) (planeEquiv A)
    (hasMFDerivAt_regularHomeomorph q A) (hasMFDerivAt_regularHomeomorph_symm q A) v x

theorem trajectory_conjugacy (v : Plane) (x : Regular q) (t : ℝ) (ht : t ∈ domain q v x) :
    regularHomeomorph q A (trajectory q v x t) =
      trajectory (transformed q A) (planeEquiv A v) (regularHomeomorph q A x) t :=
  MNEC.TranslationLinearFlowConjugacy.trajectory_conjugacy
    (regularHomeomorph q A) (planeEquiv A) (hasMFDerivAt_regularHomeomorph q A) v x t ht

theorem complete_iff (v : Plane) (x : Regular q) :
    regularHomeomorph q A x ∈ completeOrbitSet (transformed q A) (planeEquiv A v) ↔
      x ∈ completeOrbitSet q v := by
  change domain (transformed q A) (planeEquiv A v) (regularHomeomorph q A x) = univ ↔
    domain q v x = univ
  rw [domain_eq q A v x]

def completeHomeomorph (v : Plane) : CompleteOrbits q v ≃ₜ CompleteOrbits (transformed q A) (planeEquiv A v) where
  toFun x := ⟨regularHomeomorph q A x.val, (complete_iff q A v x.val).mpr x.property⟩
  invFun y := ⟨(regularHomeomorph q A).symm y.val, (complete_iff q A v _).mp (by
    simpa only [Homeomorph.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext ((regularHomeomorph q A).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((regularHomeomorph q A).apply_symm_apply y.val)
  continuous_toFun := ((regularHomeomorph q A).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((regularHomeomorph q A).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem flow_conjugacy (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    completeHomeomorph q A v (flow q v t x) =
      flow (transformed q A) (planeEquiv A v) t (completeHomeomorph q A v x) := by
  apply Subtype.ext
  exact trajectory_conjugacy q A v x.val t (complete_time_mem q v x t)

theorem surface_orbit_relation (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    (flow (transformed q A) (planeEquiv A v) t (completeHomeomorph q A v x)).val.val =
      (toOriginal q A).symm (flow q v t x).val.val := by
  exact (congrArg (fun y : CompleteOrbits (transformed q A) (planeEquiv A v) => y.val.val)
    (flow_conjugacy q A v t x)).symm

theorem orbit_dense_iff (v : Plane) (x : CompleteOrbits q v) :
    DenseRange (fun t : ℝ => (flow q v t x).val.val) ↔
      DenseRange (fun t : ℝ => (flow (transformed q A) (planeEquiv A v) t
        (completeHomeomorph q A v x)).val.val) := by
  constructor
  · intro hdense
    have h := (toOriginal q A).symm.surjective.denseRange.comp hdense (toOriginal q A).symm.continuous
    convert h using 1
    funext t
    exact surface_orbit_relation q A v t x
  · intro hdense
    have h := (toOriginal q A).surjective.denseRange.comp hdense (toOriginal q A).continuous
    simpa only [Function.comp_def, surface_orbit_relation, Homeomorph.apply_symm_apply] using h

theorem minimalDirection_iff (v : Plane) :
    NativeDynamics.MinimalDirection q v ↔
      NativeDynamics.MinimalDirection (transformed q A) (planeEquiv A v) := by
  have hne : planeEquiv A v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, map_zero]
    · intro h hv
      exact h ((planeEquiv A).injective (hv.trans (map_zero (planeEquiv A)).symm))
  constructor
  · intro h
    refine ⟨hne.mpr h.1, fun y => ?_⟩
    have hd := (orbit_dense_iff q A v ((completeHomeomorph q A v).symm y)).mp
      (h.2 ((completeHomeomorph q A v).symm y))
    simpa only [Homeomorph.apply_symm_apply] using hd
  · intro h
    exact ⟨hne.mp h.1, fun x => (orbit_dense_iff q A v x).mpr (h.2 (completeHomeomorph q A v x))⟩

end VeechDichotomy.NativeDeformationFlow
