module

public import VeechDichotomy.HolomorphicLocalInverse
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Local restriction and transition calculations for genuine complex
charts, used when constructing the changed covering-source atlas. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexAtlasTools

open Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

theorem mdifferentiable_restr (e : OpenPartialHomeomorph M N)
    (he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (S : Set M) :
    (e.restr S).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · intro x hx
    exact (he.mdifferentiableAt hx.1).mdifferentiableWithinAt
  · intro z hz
    exact (he.mdifferentiableAt_symm hz.1).mdifferentiableWithinAt

theorem transition_differentiableAt (A B : OpenPartialHomeomorph M ℂ) (z : ℂ)
    (hA : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) A.symm z)
    (hB : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) B (A.symm z)) :
    DifferentiableAt ℂ (A.symm.trans B) z := by
  exact (hB.comp z hA).differentiableAt

end VeechDichotomy.ComplexAtlasTools
