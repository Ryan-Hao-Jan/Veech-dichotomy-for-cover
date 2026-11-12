module

public import VeechDichotomy.NativeAnalyticCoverTotalSpace

/-! The actual proper holomorphic parameter projection is a submersion:
its native complex derivative is surjective at every total-space point.
This is derived from the literal first-coordinate equation of the charts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverSubmersion

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters NativeAnalyticCoverTotalSpace Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π)

theorem ambientParameter_surjective_derivative (p : TotalSpace π A hBranch) :
    Function.Surjective (mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (ambientParameter π A hBranch) p) := by
  have hc : MDifferentiableAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m × ℂ) (chart π A hBranch p) p :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, Space m × ℂ)) (chart_mem_atlas (Space m × ℂ) p) (mem_chart_source (Space m × ℂ) p)
  have hf : HasMFDerivAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m)
      (Prod.fst : Space m × ℂ → Space m) (chart π A hBranch p p) (ContinuousLinearMap.fst ℂ (Space m) ℂ) :=
    (ContinuousLinearMap.fst ℂ (Space m) ℂ).hasFDerivAt.hasMFDerivAt
  have hd : HasMFDerivAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (ambientParameter π A hBranch) p
      ((ContinuousLinearMap.fst ℂ (Space m) ℂ).comp
        (mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m × ℂ) (chart π A hBranch p) p)) :=
    (hf.comp p hc.hasMFDerivAt).congr_of_eventuallyEq_abuse
      (Filter.Eventually.of_forall fun z => (chart_parameter π A hBranch p z).symm)
  have hsurj := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Space m × ℂ))
    (chart_mem_atlas (Space m × ℂ) p)).mfderiv_surjective (mem_chart_source (Space m × ℂ) p)
  rw [hd.mfderiv]
  intro v
  obtain ⟨u, hu⟩ := hsurj (v, 0)
  exact ⟨u, congrArg Prod.fst hu⟩

theorem projection_surjective_derivative (p : TotalSpace π A hBranch) :
    Function.Surjective (mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (projection π A hBranch) p) := by
  let c := ComplexDisplacementParameters.chart m
  have hπ : MDifferentiableAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (projection π A hBranch) p :=
    (projection_holomorphic π A hBranch).mdifferentiableAt (by decide)
  have hc : MDifferentiableAt 𝓘(ℂ, Space m) 𝓘(ℂ, Space m) c (projection π A hBranch p) :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, Space m)) (chart_mem_atlas (Space m) (projection π A hBranch p))
      (mem_chart_source (Space m) (projection π A hBranch p))
  have hder : mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (ambientParameter π A hBranch) p =
      (mfderiv 𝓘(ℂ, Space m) 𝓘(ℂ, Space m) c (projection π A hBranch p)).comp
        (mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) (projection π A hBranch) p) :=
    (hc.hasMFDerivAt.comp p hπ.hasMFDerivAt).mfderiv
  have hinj := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Space m))
    (chart_mem_atlas (Space m) (projection π A hBranch p))).mfderiv_injective
      (mem_chart_source (Space m) (projection π A hBranch p))
  intro v
  obtain ⟨u, hu⟩ := ambientParameter_surjective_derivative π A hBranch p
    (mfderiv 𝓘(ℂ, Space m) 𝓘(ℂ, Space m) c (projection π A hBranch p) v)
  refine ⟨u, hinj ?_⟩
  rw [hder] at hu
  exact hu

end VeechDichotomy.NativeAnalyticCoverSubmersion
