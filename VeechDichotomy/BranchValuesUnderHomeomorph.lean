module

public import Jacobians.MappingDegree.CriticalValuesFiniteGeneral

/-! Topological critical points and values are invariant under an actual
homeomorphism of the source. The result uses literal local injectivity,
not a supplied branch-set preservation certificate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BranchValuesUnderHomeomorph

open Set Filter Topology Jacobians.Discharge.Manifold

variable {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]

theorem locally_injective_precomp_iff (f : Y → X) (H : E ≃ₜ Y) (x : E) :
    (∃ U ∈ 𝓝 x, InjOn (f ∘ H) U) ↔ ∃ V ∈ 𝓝 (H x), InjOn f V := by
  constructor
  · rintro ⟨U, hU, hinj⟩
    have ht : Tendsto H.symm (𝓝 (H x)) (𝓝 x) := by
      simpa only [Homeomorph.symm_apply_apply] using (H.symm.continuous.continuousAt (x := H x)).tendsto
    refine ⟨H.symm ⁻¹' U, ht hU, ?_⟩
    intro a ha b hb hab
    apply H.symm.injective
    apply hinj ha hb
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hab
  · rintro ⟨V, hV, hinj⟩
    refine ⟨H ⁻¹' V, H.continuous.continuousAt hV, ?_⟩
    intro a ha b hb hab
    exact H.injective (hinj ha hb hab)

theorem criticalSet_precomp (f : Y → X) (H : E ≃ₜ Y) :
    criticalSetGeneral (f ∘ H) = H ⁻¹' criticalSetGeneral f := by
  ext x
  exact not_congr (locally_injective_precomp_iff f H x)

theorem criticalValues_precomp (f : Y → X) (H : E ≃ₜ Y) :
    criticalValuesGeneral (f ∘ H) = criticalValuesGeneral f := by
  change (f ∘ H) '' criticalSetGeneral (f ∘ H) = f '' criticalSetGeneral f
  rw [criticalSet_precomp]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨H a, ha, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨H.symm y, ?_, ?_⟩
    · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hy
    · change f (H (H.symm y)) = f y
      rw [Homeomorph.apply_symm_apply]

end VeechDichotomy.BranchValuesUnderHomeomorph
