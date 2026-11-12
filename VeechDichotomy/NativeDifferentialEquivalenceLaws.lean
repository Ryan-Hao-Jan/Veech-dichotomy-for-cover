module

public import MNEC.NativeDifferentialEquiv

/-! Identity, inverse and composition for genuine native differential
equivalences. Each operation retains the actual curve homeomorphism. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDifferentialEquivalenceLaws

set_option backward.isDefEq.respectTransparency false

open MNEC.NativeAbelianDifferential MNEC.NativeDifferentialEquiv
open scoped Manifold ContDiff

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {q : Differential X} {r : Differential Y} {s : Differential Z}

def refl (q : Differential X) : Equiv q q where
  homeomorph := Homeomorph.refl X
  differentiable _ := mdifferentiableAt_id
  inverse_differentiable _ := mdifferentiableAt_id
  oneForm_pullback x := by
    change q.val.toFun x = (q.val.toFun x).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) id x)
    rw [mfderiv_id, ContinuousLinearMap.comp_id]

def symm (e : Equiv q r) : Equiv r q where
  homeomorph := e.homeomorph.symm
  differentiable := e.inverse_differentiable
  inverse_differentiable := e.differentiable
  oneForm_pullback := inverse_oneForm_pullback e

def trans (e : Equiv q r) (f : Equiv r s) : Equiv q s where
  homeomorph := e.homeomorph.trans f.homeomorph
  differentiable x := (f.differentiable (e.homeomorph x)).comp x (e.differentiable x)
  inverse_differentiable z := (e.inverse_differentiable (f.homeomorph.symm z)).comp z
    (f.inverse_differentiable z)
  oneForm_pullback x := by
    have hd := ((f.differentiable (e.homeomorph x)).hasMFDerivAt.comp x
      (e.differentiable x).hasMFDerivAt).mfderiv
    change q.val.toFun x = (s.val.toFun (f.homeomorph (e.homeomorph x))).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (f.homeomorph ∘ e.homeomorph) x)
    rw [e.oneForm_pullback, f.oneForm_pullback, ContinuousLinearMap.comp_assoc, hd]

end VeechDichotomy.NativeDifferentialEquivalenceLaws
