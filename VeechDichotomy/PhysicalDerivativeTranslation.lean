module

public import MNEC.TranslationLinearChartDerivatives
public import MNEC.FlatDerivativeGerms
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! A map between actual translation manifolds with identity physical
derivative has translation germs in their actual charts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PhysicalDerivativeTranslation

open MNEC.LatticeTorus Set Filter Topology
open scoped Manifold ContDiff

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace Plane X] [ChartedSpace Plane Y]
  [HasGroupoid X MNEC.TranslationGroupoid.groupoid]
  [HasGroupoid Y MNEC.TranslationGroupoid.groupoid]
  [IsManifold 𝓘(ℝ, Plane) ∞ X] [IsManifold 𝓘(ℝ, Plane) ∞ Y]

theorem coordinate_hasFDerivAt (F : X → Y)
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y)
    (x : X) (hx : x ∈ A.source) (hFx : F x ∈ B.source)
    (hF : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x (ContinuousLinearMap.id ℝ Plane)) :
    HasFDerivAt (fun p : Plane => B (F (A.symm p)))
      (ContinuousLinearMap.id ℝ Plane) (A x) := by
  have hAi := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) hA (A.map_source hx)).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_symm_id A hA _ (A.map_source hx)] at hAi
  have hF' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F (A.symm (A x))
      (ContinuousLinearMap.id ℝ Plane) := by rwa [A.left_inv hx]
  have hBo := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) hB hFx).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_id B hB _ hFx] at hBo
  have hBo' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) B (F (A.symm (A x)))
      (ContinuousLinearMap.id ℝ Plane) := by rwa [A.left_inv hx]
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using!
    (hBo'.comp (A x) (hF'.comp (A x) hAi)).hasFDerivAt

theorem map_translation_germ (F : X → Y) (hc : Continuous F)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x
      (ContinuousLinearMap.id ℝ Plane))
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y)
    (x : X) (hx : x ∈ A.source) (hFx : F x ∈ B.source) :
    ∃ a : Plane, ∀ᶠ y in 𝓝 x, B (F y) = A y + a := by
  let T : Plane → Plane := fun p => B (F (A.symm p))
  let U := A.target ∩ (F ∘ A.symm) ⁻¹' B.source
  have hU : IsOpen U :=
    (hc.comp_continuousOn A.symm.continuousOn).isOpen_inter_preimage A.open_target B.open_source
  have hT : ∀ p ∈ U, HasFDerivAt T (ContinuousLinearMap.id ℝ Plane) p := by
    intro p hp
    have hd := coordinate_hasFDerivAt F A B hA hB (A.symm p) (A.map_target hp.1) hp.2 (hF _)
    rw [A.right_inv hp.1] at hd
    exact hd
  have hp : A x ∈ U := by
    refine ⟨A.map_source hx, ?_⟩
    change F (A.symm (A x)) ∈ B.source
    rwa [A.left_inv hx]
  have hg := MNEC.FlatDerivativeGerms.translation_germ_of_derivative_id
    T U hU hT (A x) hp
  have hnear := (A.continuousAt hx) hg
  refine ⟨T (A x) - A x, ?_⟩
  filter_upwards [A.open_source.mem_nhds hx, hnear] with y hy heq
  change B (F (A.symm (A y))) = A y + _ at heq
  rwa [A.left_inv hy] at heq

theorem translation_germ (F : X ≃ₜ Y)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x
      (ContinuousLinearMap.id ℝ Plane))
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y)
    (x : X) (hx : x ∈ A.source) (hFx : F x ∈ B.source) :
    ∃ a : Plane, ∀ᶠ y in 𝓝 x, B (F y) = A y + a :=
  map_translation_germ F F.continuous hF A B hA hB x hx hFx

end VeechDichotomy.PhysicalDerivativeTranslation
