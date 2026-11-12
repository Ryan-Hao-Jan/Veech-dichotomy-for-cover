module

public import MNEC.NativeDifferentialEquivArea
public import MNEC.TranslationFlowConjugacy
public import MNEC.NativeDirectionalDynamics

/-! A genuine one-form-preserving curve isomorphism is a physical
translation on both regular loci. Its real native derivatives are the
identity; maximal directional domains and trajectories consequently
agree by the native ODE uniqueness theorem. No flatness or dynamics
identity is supplied as an input. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeDifferentialEquivFlatness

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativeDifferentialEquiv NativeDifferentialEquivArea Set Filter Topology
open scoped Manifold ContDiff Classical

set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y}

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : ChartedSpace Plane (Regular r) := chartedSpace r
local instance : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
local instance : HasGroupoid (Regular r) TranslationGroupoid.groupoid := has_translation_groupoid r
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := isManifold q ∞
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular r) := isManifold r ∞

def reverse (e : Equiv q r) : Equiv r q where
  homeomorph := e.homeomorph.symm
  differentiable := e.inverse_differentiable
  inverse_differentiable := e.differentiable
  oneForm_pullback := inverse_oneForm_pullback e

theorem reverse_regularHomeomorph (e : Equiv q r) :
    regularHomeomorph (reverse e) = (regularHomeomorph e).symm := rfl

theorem forward_translation_germ (e : Equiv q r) (x : Regular q) : ∃ a : Plane,
    coordinateChart q x x + a ∈ (coordinateChart r (regularHomeomorph e x)).target ∧
      ∀ᶠ y in 𝓝 x, regularHomeomorph e y =
        (coordinateChart r (regularHomeomorph e x)).symm (coordinateChart q x y + a) := by
  let A := coordinateChart q x
  let B := coordinateChart r (regularHomeomorph e x)
  let P := NativePrimitiveAreaCharts.chart q (pulledIndex e x)
  have hA : x ∈ A.source := coordinateChart_center q x
  have hP : x ∈ P.source := by
    rw [NativePrimitiveAreaCharts.chart_source]
    exact (pulledPrimitive e x).center
  have hp : A x ∈ (A.symm.trans P).source := by
    refine ⟨A.map_source hA, ?_⟩
    change A.symm (A x) ∈ P.source
    rw [A.left_inv hA]
    exact hP
  obtain ⟨a, ha⟩ := NativePrimitiveAreaCharts.transition_locally_translation q
    (NativePrimitiveAreaCharts.selectedIndex q x) (pulledIndex e x) (A x) hp
  have hcont : ContinuousAt A x := A.continuousOn.continuousAt (A.open_source.mem_nhds hA)
  have hcoord : ∀ᶠ y in 𝓝 x, B (regularHomeomorph e y) = A y + a := by
    filter_upwards [A.open_source.mem_nhds hA, hcont ha] with y hy htrans
    change P (A.symm (A y)) = A y + a at htrans
    rw [A.left_inv hy] at htrans
    exact (pulled_chart_apply e x y).symm.trans htrans
  have hB : regularHomeomorph e x ∈ B.source := coordinateChart_center r _
  refine ⟨a, ?_, ?_⟩
  · rw [← hcoord.self_of_nhds]
    exact B.map_source hB
  · filter_upwards [hcoord, (regularHomeomorph e).continuous.continuousAt
      (B.open_source.mem_nhds hB)] with y hy hys
    calc
      regularHomeomorph e y = B.symm (B (regularHomeomorph e y)) := (B.left_inv hys).symm
      _ = _ := by rw [hy]

theorem hasMFDerivAt_regularHomeomorph (e : Equiv q r) (x : Regular q) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph e) x
      (ContinuousLinearMap.id ℝ Plane) := by
  obtain ⟨a, htarget, hfactor⟩ := forward_translation_germ e x
  let A := coordinateChart q x
  let B := coordinateChart r (regularHomeomorph e x)
  have he : A ∈ atlas Plane (Regular q) := ⟨x, rfl⟩
  have hd : B ∈ atlas Plane (Regular r) := ⟨regularHomeomorph e x, rfl⟩
  have hi := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) he
    (coordinateChart_center q x)).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_id A he x (coordinateChart_center q x)] at hi
  have ht : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (fun p : Plane => p + a)
      (A x) (ContinuousLinearMap.id ℝ Plane) := ((hasFDerivAt_id _).add_const a).hasMFDerivAt
  have hj := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) hd htarget).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_symm_id B hd _ htarget] at hj
  have hcomp := hj.comp x (ht.comp x hi)
  simpa only [ContinuousLinearMap.id_comp] using! hcomp.congr_of_eventuallyEq_abuse hfactor

theorem hasMFDerivAt_regularHomeomorph_symm (e : Equiv q r) (y : Regular r) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph e).symm y
      (ContinuousLinearMap.id ℝ Plane) := by
  rw [← reverse_regularHomeomorph e]
  exact hasMFDerivAt_regularHomeomorph (reverse e) y

theorem domain_eq (e : Equiv q r) (v : Plane) (x : Regular q) :
    NativeDirectionalDynamics.domain q v x =
      NativeDirectionalDynamics.domain r v (regularHomeomorph e x) :=
  TranslationFlowConjugacy.domain_eq (regularHomeomorph e)
    (hasMFDerivAt_regularHomeomorph e) (hasMFDerivAt_regularHomeomorph_symm e) v x

theorem trajectory_conjugacy (e : Equiv q r) (v : Plane) (x : Regular q) (t : ℝ)
    (ht : t ∈ NativeDirectionalDynamics.domain q v x) :
    regularHomeomorph e (NativeDirectionalDynamics.trajectory q v x t) =
      NativeDirectionalDynamics.trajectory r v (regularHomeomorph e x) t :=
  TranslationFlowConjugacy.trajectory_conjugacy (regularHomeomorph e)
    (hasMFDerivAt_regularHomeomorph e) v x t ht

end MNEC.NativeDifferentialEquivFlatness

