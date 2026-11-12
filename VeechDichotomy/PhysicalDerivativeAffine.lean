module

public import VeechDichotomy.PhysicalDerivativeTranslation

/-! A constant actual physical derivative gives exact affine germs in
genuine translation charts. The ordinary vector-valued mean value theorem
proves the affine identity; no affine coordinate formula is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PhysicalDerivativeAffine

open MNEC.LatticeTorus Set Filter Topology
open scoped Manifold ContDiff

theorem affine_germ_of_derivative (f : Plane → Plane) (L : Plane →L[ℝ] Plane) (U : Set Plane)
    (hU : IsOpen U) (hder : ∀ y ∈ U, HasFDerivAt f L y) (x : Plane) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, f y = L y + (f x - L x) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let g : Plane → Plane := fun y => L y + (f x - L x)
  have hf : DifferentiableOn ℝ f (Metric.ball x r) :=
    fun y hy => (hder y (hball hy)).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ g (Metric.ball x r) := (L.differentiable.add_const _).differentiableOn
  have hdf : (Metric.ball x r).EqOn (fderivWithin ℝ f (Metric.ball x r)) (fderivWithin ℝ g (Metric.ball x r)) := by
    intro y hy
    have hfy := (hder y (hball hy)).fderiv
    have hgy : fderiv ℝ g y = L := (L.hasFDerivAt.add_const _).fderiv
    simpa only [fderivWithin_of_isOpen Metric.isOpen_ball hy] using hfy.trans hgy.symm
  have heq : (Metric.ball x r).EqOn f g :=
    (convex_ball x r).eqOn_of_fderivWithin_eq hf hg Metric.isOpen_ball.uniqueDiffOn hdf
      (Metric.mem_ball_self hr) (by dsimp [g]; abel)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with y hy
  exact heq hy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace Plane X] [ChartedSpace Plane Y]
  [HasGroupoid X MNEC.TranslationGroupoid.groupoid] [HasGroupoid Y MNEC.TranslationGroupoid.groupoid]
  [IsManifold 𝓘(ℝ, Plane) ∞ X] [IsManifold 𝓘(ℝ, Plane) ∞ Y]

theorem coordinate_hasFDerivAt (F : X → Y) (L : Plane →L[ℝ] Plane)
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y) (x : X) (hx : x ∈ A.source) (hFx : F x ∈ B.source)
    (hF : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x L) :
    HasFDerivAt (fun p : Plane => B (F (A.symm p))) L (A x) := by
  have hAi := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) hA (A.map_source hx)).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_symm_id A hA _ (A.map_source hx)] at hAi
  have hF' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F (A.symm (A x)) L := by rwa [A.left_inv hx]
  have hBo := (mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) hB hFx).hasMFDerivAt
  rw [MNEC.TranslationAtlasField.mfderiv_atlas_id B hB _ hFx] at hBo
  have hBo' : HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) B (F (A.symm (A x))) (ContinuousLinearMap.id ℝ Plane) := by
    rwa [A.left_inv hx]
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, Function.comp_def] using!
    (hBo'.comp (A x) (hF'.comp (A x) hAi)).hasFDerivAt

theorem map_affine_germ (F : X → Y) (hc : Continuous F) (L : Plane →L[ℝ] Plane)
    (hF : ∀ x, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) F x L)
    (A : OpenPartialHomeomorph X Plane) (B : OpenPartialHomeomorph Y Plane)
    (hA : A ∈ atlas Plane X) (hB : B ∈ atlas Plane Y) (x : X) (hx : x ∈ A.source) (hFx : F x ∈ B.source) :
    ∀ᶠ y in 𝓝 x, B (F y) = L (A y) + (B (F x) - L (A x)) := by
  let T : Plane → Plane := fun p => B (F (A.symm p))
  let U := A.target ∩ (F ∘ A.symm) ⁻¹' B.source
  have hU : IsOpen U := (hc.comp_continuousOn A.symm.continuousOn).isOpen_inter_preimage A.open_target B.open_source
  have hT : ∀ p ∈ U, HasFDerivAt T L p := by
    intro p hp
    have hd := coordinate_hasFDerivAt F L A B hA hB (A.symm p) (A.map_target hp.1) hp.2 (hF _)
    rwa [A.right_inv hp.1] at hd
  have hxU : A x ∈ U := by
    refine ⟨A.map_source hx, ?_⟩
    change F (A.symm (A x)) ∈ B.source
    rwa [A.left_inv hx]
  have hg := affine_germ_of_derivative T L U hU hT (A x) hxU
  filter_upwards [A.open_source.mem_nhds hx, (A.continuousAt hx) hg] with y hy heq
  change B (F (A.symm (A y))) = L (A y) + (B (F (A.symm (A x))) - L (A x)) at heq
  simpa only [A.left_inv hx, A.left_inv hy] using heq

end VeechDichotomy.PhysicalDerivativeAffine
