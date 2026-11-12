module

public import MNEC.TranslationPartialFlow
public import MNEC.FlatDerivativeGerms
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Actual fixed-time partial maps are locally physical translations

Every accepted ball step has native identity tangent derivative by the
proved atlas derivatives. Finite composition and the actual word formula
give this derivative for the actual maximal time map. In any accepted
physical coordinates the ordinary derivative is identity, and the native
mean-value theorem gives the genuine translation germ.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationFlowDifferentials

open LatticeTorus TranslationBallCharts TranslationFlowWords Set Topology Filter
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]
variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X]

theorem ballTimeMap_hasMFDerivAt (B : BallChart X) (v : Plane) (t : ℝ) (x : X)
    (hx : x ∈ (timeMap B v t).source) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (timeMap B v t) x (ContinuousLinearMap.id ℝ Plane) := by
  obtain ⟨hxB, ht⟩ := (mem_timeMap_source B v t x).mp hx
  have hxC := target_subset_chartSource B hxB
  have hy : B.chart x + t • v ∈ B.chart.target := B.ball_subset ht
  have hchart := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) B.mem_atlas hxC).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_id B.chart B.mem_atlas x hxC] at hchart
  have hadd : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (fun p : Plane => p + t • v) (B.chart x)
      (ContinuousLinearMap.id ℝ Plane) := ((hasFDerivAt_id (B.chart x)).add_const (t • v)).hasMFDerivAt
  have hinverse := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) B.mem_atlas hy).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_symm_id B.chart B.mem_atlas _ hy] at hinverse
  have hcomp := hinverse.comp x (hadd.comp x hchart)
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using! hcomp

theorem wordMap_hasMFDerivAt (v : Plane) (W : List (Step X)) (x : X) (hx : x ∈ (wordMap v W).source) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (wordMap v W) x (ContinuousLinearMap.id ℝ Plane) := by
  induction W generalizing x with
  | nil => exact hasMFDerivAt_id x
  | cons S W ih =>
    have hfirst := ballTimeMap_hasMFDerivAt S.1 v S.2 x hx.1
    have hrest := ih (timeMap S.1 v S.2 x) hx.2
    have hcomp := hrest.comp x hfirst
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using! hcomp

theorem coordinate_hasFDerivAt_id (F : X → X) (e f : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (hf : f ∈ atlas Plane X) (x : X) (hx : x ∈ e.source) (hFx : F x ∈ f.source)
    (hF : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x (ContinuousLinearMap.id ℝ Plane)) :
    HasFDerivAt (fun p : Plane => f (F (e.symm p))) (ContinuousLinearMap.id ℝ Plane) (e x) := by
  have hex : e x ∈ e.target := e.map_source hx
  have hei := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) he hex).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_symm_id e he (e x) hex] at hei
  have hF' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F (e.symm (e x)) (ContinuousLinearMap.id ℝ Plane) := by
    rw [e.left_inv hx]
    exact hF
  have hfo := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) hf hFx).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_id f hf (F x) hFx] at hfo
  have hfo' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f (F (e.symm (e x))) (ContinuousLinearMap.id ℝ Plane) := by
    rw [e.left_inv hx]
    exact hfo
  have hcomp := hfo'.comp (e x) (hF'.comp (e x) hei)
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using! hcomp.hasFDerivAt

variable [T2Space X]

theorem timeMap_hasMFDerivAt (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (TranslationPartialFlow.timeMap v t).source) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (TranslationPartialFlow.timeMap v t) x (ContinuousLinearMap.id ℝ Plane) := by
  obtain ⟨W, _, hW, heq⟩ := TranslationPartialFlow.timeMap_locally_word v t x hx
  exact (wordMap_hasMFDerivAt v W x hW).congr_of_eventuallyEq_abuse heq

theorem coordinate_timeMap_hasFDerivAt (v : Plane) (t : ℝ) (e f : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (hf : f ∈ atlas Plane X) (p : Plane)
    (hp : p ∈ (e.symm.trans ((TranslationPartialFlow.timeMap v t).trans f)).source) :
    HasFDerivAt (e.symm.trans ((TranslationPartialFlow.timeMap v t).trans f)) (ContinuousLinearMap.id ℝ Plane) p := by
  have hcoord := coordinate_hasFDerivAt_id (TranslationPartialFlow.timeMap v t) e f he hf (e.symm p)
    (e.map_target hp.1) hp.2.2 (timeMap_hasMFDerivAt v t (e.symm p) hp.2.1)
  rw [e.right_inv hp.1] at hcoord
  exact hcoord

/-- The actual maximal time map has a physical translation germ in every
accepted source/target pair of atlas charts. -/
theorem timeMap_locally_physical_translation (v : Plane) (t : ℝ) (e f : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (hf : f ∈ atlas Plane X) (x : X)
    (hx : x ∈ (TranslationPartialFlow.timeMap v t).source) (hxe : x ∈ e.source)
    (hxf : TranslationPartialFlow.timeMap v t x ∈ f.source) :
    ∃ c : Plane, ∀ᶠ p in 𝓝 (e x), f (TranslationPartialFlow.timeMap v t (e.symm p)) = p + c := by
  let T := e.symm.trans ((TranslationPartialFlow.timeMap v t).trans f)
  have hp : e x ∈ T.source := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ ((TranslationPartialFlow.timeMap v t).trans f).source
    rw [e.left_inv hxe]
    exact ⟨hx, hxf⟩
  exact ⟨T (e x) - e x, FlatDerivativeGerms.translation_germ_of_derivative_id T T.source T.open_source
    (fun p hp => coordinate_timeMap_hasFDerivAt v t e f he hf p hp) (e x) hp⟩

end MNEC.TranslationFlowDifferentials

