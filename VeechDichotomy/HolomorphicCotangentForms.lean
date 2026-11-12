module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.Hom

/-! Holomorphic cotangent sections on complex manifolds of arbitrary model
dimension. The pullback proof generalizes the checked curve-only proof in
Jacobians.Forms.HolomorphicForms; no compactness, curve dimension, or added
analytic assumption is required. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCotangentForms

open Set Filter Topology
open scoped Manifold ContDiff Bundle

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

abbrev Form := ContMDiffSection 𝓘(ℂ, E) (E →L[ℂ] ℂ) ω
  (fun x : M => TangentSpace 𝓘(ℂ, E) x →L[ℂ] (Bundle.Trivial M ℂ) x)

variable {E M}
variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]

def pullback (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) : Form F N →ₗ[ℂ] Form E M where
  toFun α :=
    { toFun := fun x => (α.toFun (f x)).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)
      contMDiff_toFun := by
        intro x₀
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        have hA : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F →L[ℂ] ℂ) ω
            (fun x => ContinuousLinearMap.inCoordinates F
              (TangentSpace 𝓘(ℂ, F) (M := N)) ℂ (Bundle.Trivial N ℂ)
              (f x₀) (f x) (f x₀) (f x) (α.toFun (f x))) x₀ := by
          have hα := α.contMDiff_toFun (f x₀)
          rw [contMDiffAt_hom_bundle] at hα
          exact hα.2.comp x₀ (hf x₀)
        have hB : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E →L[ℂ] F) ω
            (fun x => ContinuousLinearMap.inCoordinates E
              (TangentSpace 𝓘(ℂ, E) (M := M)) F (TangentSpace 𝓘(ℂ, F) (M := N))
              x₀ x (f x₀) (f x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)) x₀ :=
          (hf x₀).mfderiv_const (le_refl _)
        have hcomp : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E →L[ℂ] ℂ) ω
            (fun x => (ContinuousLinearMap.inCoordinates F
                (TangentSpace 𝓘(ℂ, F) (M := N)) ℂ (Bundle.Trivial N ℂ)
                (f x₀) (f x) (f x₀) (f x) (α.toFun (f x))).comp
              (ContinuousLinearMap.inCoordinates E
                (TangentSpace 𝓘(ℂ, E) (M := M)) F (TangentSpace 𝓘(ℂ, F) (M := N))
                x₀ x (f x₀) (f x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))) x₀ := hA.clm_comp hB
        apply hcomp.congr_of_eventuallyEq
        filter_upwards [
          (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := M)) x₀).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt E _ x₀),
          hf.continuous.continuousAt.preimage_mem_nhds
            ((trivializationAt F (TangentSpace 𝓘(ℂ, F) (M := N)) (f x₀)).open_baseSet.mem_nhds
              (mem_baseSet_trivializationAt F _ (f x₀)))] with x hxM hxN
        ext v
        simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
          Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_apply]
        rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxN] }
  map_add' _ _ := by
    apply ContMDiffSection.ext
    intro x
    rfl
  map_smul' _ _ := by
    apply ContMDiffSection.ext
    intro x
    rfl

@[simp] theorem pullback_value (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (α : Form F N) (x : M) : (pullback f hf α).toFun x =
    (α.toFun (f x)).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) := rfl

theorem pullback_id (α : Form E M) : pullback (id : M → M) contMDiff_id α = α := by
  apply ContMDiffSection.ext
  intro x
  change (α.toFun x).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) id x) = α.toFun x
  rw [mfderiv_id, ContinuousLinearMap.comp_id]

variable {G P : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℂ, G) ω P]

theorem pullback_comp (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (g : N → P) (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ω g) (α : Form G P) :
    pullback f hf (pullback g hg α) = pullback (g ∘ f) (hg.comp hf) α := by
  apply ContMDiffSection.ext
  intro x
  change ((α.toFun (g (f x))).comp (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, G) g (f x))).comp
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) =
    (α.toFun (g (f x))).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (g ∘ f) x)
  rw [mfderiv_comp x (hg.mdifferentiableAt (by decide)) (hf.mdifferentiableAt (by decide)),
    ContinuousLinearMap.comp_assoc]

end VeechDichotomy.HolomorphicCotangentForms
