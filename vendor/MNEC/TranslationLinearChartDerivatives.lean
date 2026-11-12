module

public import MNEC.TranslationAtlasField
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! Native forward/inverse derivatives from an ACTUAL coordinate
homeomorphism derivative G. Inverse differentiability follows from the
proved ordinary inverse rule and chart identities; it is not supplied. -/

@[expose] public section
noncomputable section
namespace MNEC.TranslationLinearChartDerivatives

open LatticeTorus Set Topology Filter
open scoped Manifold ContDiff
set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def coordinate (f : X ≃ₜ Y) (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane) :
    OpenPartialHomeomorph Plane Plane := (A.symm.transHomeomorph f).trans B

variable [ChartedSpace Plane X] [ChartedSpace Plane Y]
  [HasGroupoid X TranslationGroupoid.groupoid] [HasGroupoid Y TranslationGroupoid.groupoid]
  [IsManifold 𝓘(ℝ, Plane) ∞ X] [IsManifold 𝓘(ℝ, Plane) ∞ Y]

theorem hasMFDerivAt_of_coordinate (f : X ≃ₜ Y) (G : Plane ≃L[ℝ] Plane)
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y)
    (x : X) (hxA : x ∈ A.source) (hxB : f x ∈ B.source)
    (hT : HasFDerivAt (coordinate f A B) G.toContinuousLinearMap (A x)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x G.toContinuousLinearMap := by
  have hvalue : coordinate f A B (A x) = B (f x) := by
    change B (f (A.symm (A x))) = B (f x)
    rw [A.left_inv hxA]
  have hi := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) hA hxA).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_id A hA x hxA] at hi
  have hj := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) hB (B.map_source hxB)).hasMFDerivAt
  rw [TranslationAtlasField.mfderiv_atlas_symm_id B hB _ (B.map_source hxB), ← hvalue] at hj
  have hcomp := hj.comp x (hT.hasMFDerivAt.comp x hi)
  have hfactor : (f : X → Y) =ᶠ[𝓝 x] fun y => B.symm (coordinate f A B (A y)) := by
    filter_upwards [A.open_source.mem_nhds hxA,
      f.continuous.continuousAt (B.open_source.mem_nhds hxB)] with y hyA hyB
    change f y = B.symm (B (f (A.symm (A y))))
    rw [A.left_inv hyA, B.left_inv hyB]
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, Function.comp_def] using!
    hcomp.congr_of_eventuallyEq_abuse hfactor

theorem hasMFDerivAt_symm_of_coordinate (f : X ≃ₜ Y) (G : Plane ≃L[ℝ] Plane)
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y)
    (x : X) (hxA : x ∈ A.source) (hxB : f x ∈ B.source)
    (hT : HasFDerivAt (coordinate f A B) G.toContinuousLinearMap (A x)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f.symm (f x) G.symm.toContinuousLinearMap := by
  let T := coordinate f A B
  have hp : A x ∈ T.source := ⟨A.map_source hxA, by change B.source (f (A.symm (A x))); rwa [A.left_inv hxA]⟩
  have hvalue : T (A x) = B (f x) := by
    change B (f (A.symm (A x))) = B (f x)
    rw [A.left_inv hxA]
  have htarget : B (f x) ∈ T.target := hvalue ▸ T.map_source hp
  have hinverse : T.symm (B (f x)) = A x := by rw [← hvalue]; exact T.left_inv hp
  have hInv := T.hasFDerivAt_symm (f' := G) htarget (by simpa only [hinverse] using hT)
  have hcoords : coordinate f.symm B A = T.symm := rfl
  rw [← hcoords] at hInv
  exact hasMFDerivAt_of_coordinate f.symm G.symm B A hB hA (f x) hxB
    (by simpa only [Homeomorph.symm_apply_apply] using hxA) hInv

end MNEC.TranslationLinearChartDerivatives

