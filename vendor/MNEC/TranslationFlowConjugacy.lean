module

public import MNEC.TranslationAtlasCurves

/-! Exact native maximal-curve conjugacy between TWO genuine translation
manifolds. The identity-derivative premises are explicit analytic inputs
to this general theorem; actual geometric callers must prove them from
their physical charts. Native ODE composition and maximality derive the
actual domain/trajectory equalities, rather than storing them as fields. -/

@[expose] public section
noncomputable section
namespace MNEC.TranslationFlowConjugacy

open LatticeTorus Set Topology
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace Plane X] [ChartedSpace Plane Y]
  [HasGroupoid X TranslationGroupoid.groupoid] [HasGroupoid Y TranslationGroupoid.groupoid]
  [IsManifold 𝓘(ℝ, Plane) ∞ X] [IsManifold 𝓘(ℝ, Plane) ∞ Y] [T2Space X] [T2Space Y]

omit [T2Space X] [T2Space Y] in
theorem mapped_integralCurveOn (f : X → Y)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x (ContinuousLinearMap.id ℝ Plane))
    (v : Plane) (γ : ℝ → X) (U : Set ℝ) :
    IsMIntegralCurveOn γ (TranslationAtlasField.field (X := X) v) U →
      IsMIntegralCurveOn (fun t => f (γ t)) (TranslationAtlasField.field (X := Y) v) U := by
  intro hγ t ht
  have hbase := hγ t ht
  rw [TranslationAtlasField.field_eq_const] at hbase
  rw [TranslationAtlasField.field_eq_const]
  have hcomp := (hF (γ t)).comp_hasMFDerivWithinAt t hbase
  simpa only [Function.comp_def, ContinuousLinearMap.id_comp] using! hcomp

theorem mapped_domain_subset_and_trajectory (f : X → Y)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x (ContinuousLinearMap.id ℝ Plane))
    (v : Plane) (x : X) :
    TranslationAtlasCurves.domain v x ⊆ TranslationAtlasCurves.domain v (f x) ∧
      EqOn (TranslationAtlasCurves.trajectory v (f x))
        (fun t => f (TranslationAtlasCurves.trajectory v x t)) (TranslationAtlasCurves.domain v x) := by
  apply TranslationAtlasCurves.extends_every_open_interval v (f x)
    (TranslationAtlasCurves.domain v x) (fun t => f (TranslationAtlasCurves.trajectory v x t))
  · exact TranslationAtlasCurves.domain_open v x
  · exact TranslationAtlasCurves.domain_ordConnected v x
  · exact TranslationAtlasCurves.zero_mem_domain v x
  · rw [TranslationAtlasCurves.trajectory_initial]
  · exact mapped_integralCurveOn f hF v _ _ (TranslationAtlasCurves.trajectory_isMIntegralCurveOn v x)

theorem domain_eq (f : X ≃ₜ Y)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x (ContinuousLinearMap.id ℝ Plane))
    (hInv : ∀ y : Y, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f.symm y (ContinuousLinearMap.id ℝ Plane))
    (v : Plane) (x : X) :
    TranslationAtlasCurves.domain v x = TranslationAtlasCurves.domain v (f x) := by
  apply Subset.antisymm
  · exact (mapped_domain_subset_and_trajectory f hF v x).1
  · have hback := (mapped_domain_subset_and_trajectory f.symm hInv v (f x)).1
    simpa only [Homeomorph.symm_apply_apply] using hback

theorem trajectory_conjugacy (f : X → Y)
    (hF : ∀ x : X, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) f x (ContinuousLinearMap.id ℝ Plane))
    (v : Plane) (x : X) (t : ℝ) (ht : t ∈ TranslationAtlasCurves.domain v x) :
    f (TranslationAtlasCurves.trajectory v x t) = TranslationAtlasCurves.trajectory v (f x) t :=
  ((mapped_domain_subset_and_trajectory f hF v x).2 ht).symm

end MNEC.TranslationFlowConjugacy

