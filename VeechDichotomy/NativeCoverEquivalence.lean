module

public import VeechDichotomy.NativeCoverBranchTopology
public import VeechDichotomy.NativeDifferentialEquivalenceLaws

/-! Postcomposing a genuine finite translation cover by a genuine native
differential equivalence constructs a cover of the identified base. Its
critical points and branch values are proved from the actual maps. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverEquivalence

open MNEC.NativeAbelianDifferential MNEC.NativeDifferentialEquiv
open NativeTranslationCover NativeCoverBranchTopology Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {q : Differential X} {r : Differential Y} {s : Differential Z}

theorem equivalence_holomorphic (e : Equiv q s) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.homeomorph :=
  HolomorphicCurveMaps.contMDiff_of_mdifferentiable e.homeomorph e.differentiable

def postcompose (π : Cover q r) (e : Equiv q s) : Cover s r where
  map := e.homeomorph ∘ π.map
  holomorphic := (equivalence_holomorphic e).comp π.holomorphic
  surjective := e.homeomorph.surjective.comp π.surjective
  finite_fibers z := by
    apply (π.finite_fibers (e.homeomorph.symm z)).subset
    intro y hy
    change π.map y = e.homeomorph.symm z
    apply e.homeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    exact hy
  pullback_eq := by
    apply ContMDiffSection.ext
    intro y
    change (s.val.toFun (e.homeomorph (π.map y))).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (e.homeomorph ∘ π.map) y) = r.val.toFun y
    rw [mfderiv_comp y (e.differentiable (π.map y))
      (π.holomorphic.mdifferentiableAt (by decide))]
    rw [← ContinuousLinearMap.comp_assoc, ← e.oneForm_pullback, ← pullback_at π y]

theorem criticalSet_postcompose (π : Cover q r) (e : Equiv q s) :
    criticalSet (postcompose π e) = criticalSet π := by
  ext y
  rw [critical_iff_not_locally_injective, critical_iff_not_locally_injective]
  apply not_congr
  constructor
  · rintro ⟨U, hU, hinj⟩
    refine ⟨U, hU, ?_⟩
    intro a ha b hb hab
    exact hinj ha hb (congrArg e.homeomorph hab)
  · rintro ⟨U, hU, hinj⟩
    refine ⟨U, hU, ?_⟩
    intro a ha b hb hab
    exact hinj ha hb (e.homeomorph.injective hab)

theorem branchValues_postcompose (π : Cover q r) (e : Equiv q s) :
    branchValues (postcompose π e) = e.homeomorph '' branchValues π := by
  change (e.homeomorph ∘ π.map) '' criticalSet (postcompose π e) = _
  rw [criticalSet_postcompose]
  exact (image_image e.homeomorph π.map (criticalSet π)).symm

end VeechDichotomy.NativeCoverEquivalence
