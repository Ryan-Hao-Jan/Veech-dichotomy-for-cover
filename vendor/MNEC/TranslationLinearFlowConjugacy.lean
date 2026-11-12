module

public import MNEC.TranslationAtlasCurves

/-! Native ODE/maximality transport through a map of constant invertible
real derivative G. These generic analytic derivative hypotheses are
proved for computed geometric maps by separate factories; no dynamics
or domain agreement is a hypothesis or structure field. -/

@[expose] public section
noncomputable section
namespace MNEC.TranslationLinearFlowConjugacy

open LatticeTorus Set Topology
open scoped Manifold ContDiff
set_option autoImplicit false

theorem comp_smulRight {R A V W : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSpace A] [AddCommMonoid A] [Module R A]
    [TopologicalSpace V] [AddCommMonoid V] [Module R V] [ContinuousSMul R V]
    [TopologicalSpace W] [AddCommMonoid W] [Module R W] [ContinuousSMul R W]
    (G : V →L[R] W) (c : A →L[R] R) (v : V) :
    G.comp (c.smulRight v) = c.smulRight (G v) := by
  apply ContinuousLinearMap.ext
  intro a
  change G (c a • v) = c a • G v
  exact G.map_smul (c a) v

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace Plane X] [ChartedSpace Plane Y]
  [HasGroupoid X TranslationGroupoid.groupoid] [HasGroupoid Y TranslationGroupoid.groupoid]
  [IsManifold 𝓘(ℝ, Plane) ∞ X] [IsManifold 𝓘(ℝ, Plane) ∞ Y] [T2Space X] [T2Space Y]

omit [T2Space X] [T2Space Y] in
theorem mapped_integralCurveOn (f : X → Y) (G : Plane ≃L[ℝ] Plane)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x G.toContinuousLinearMap)
    (v : Plane) (γ : ℝ → X) (U : Set ℝ) :
    IsMIntegralCurveOn γ (TranslationAtlasField.field (X := X) v) U →
      IsMIntegralCurveOn (fun t => f (γ t)) (TranslationAtlasField.field (X := Y) (G v)) U := by
  intro hγ t ht
  have hbase := hγ t ht
  rw [TranslationAtlasField.field_eq_const] at hbase
  rw [TranslationAtlasField.field_eq_const]
  have hcomp := (hF (γ t)).comp_hasMFDerivWithinAt t hbase
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  exact G.map_smul _ v

theorem mapped_domain_subset_and_trajectory (f : X → Y) (G : Plane ≃L[ℝ] Plane)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x G.toContinuousLinearMap)
    (v : Plane) (x : X) :
    TranslationAtlasCurves.domain v x ⊆ TranslationAtlasCurves.domain (G v) (f x) ∧
      EqOn (TranslationAtlasCurves.trajectory (G v) (f x))
        (fun t => f (TranslationAtlasCurves.trajectory v x t)) (TranslationAtlasCurves.domain v x) := by
  apply TranslationAtlasCurves.extends_every_open_interval (G v) (f x)
    (TranslationAtlasCurves.domain v x) (fun t => f (TranslationAtlasCurves.trajectory v x t))
  · exact TranslationAtlasCurves.domain_open v x
  · exact TranslationAtlasCurves.domain_ordConnected v x
  · exact TranslationAtlasCurves.zero_mem_domain v x
  · rw [TranslationAtlasCurves.trajectory_initial]
  · exact mapped_integralCurveOn f G hF v _ _ (TranslationAtlasCurves.trajectory_isMIntegralCurveOn v x)

theorem domain_eq (f : X ≃ₜ Y) (G : Plane ≃L[ℝ] Plane)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x G.toContinuousLinearMap)
    (hInv : ∀ y : Y, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f.symm y G.symm.toContinuousLinearMap)
    (v : Plane) (x : X) :
    TranslationAtlasCurves.domain v x = TranslationAtlasCurves.domain (G v) (f x) := by
  apply Subset.antisymm
  · exact (mapped_domain_subset_and_trajectory f G hF v x).1
  · have hback := (mapped_domain_subset_and_trajectory f.symm G.symm hInv (G v) (f x)).1
    simpa only [Homeomorph.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply] using hback

theorem trajectory_conjugacy (f : X → Y) (G : Plane ≃L[ℝ] Plane)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x G.toContinuousLinearMap)
    (v : Plane) (x : X) (t : ℝ) (ht : t ∈ TranslationAtlasCurves.domain v x) :
    f (TranslationAtlasCurves.trajectory v x t) = TranslationAtlasCurves.trajectory (G v) (f x) t :=
  ((mapped_domain_subset_and_trajectory f G hF v x).2 ht).symm

end MNEC.TranslationLinearFlowConjugacy

