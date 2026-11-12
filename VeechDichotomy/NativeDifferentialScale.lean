module

public import VeechDichotomy.NativeDifferentialEquivalenceLaws
public import VeechDichotomy.NativeFullCoverDegree
public import VeechDichotomy.NonzeroComplexParameter

/-! Nonzero scalar multiplication of actual native differentials,
genuine differential equivalences and finite translation covers. The
underlying curves and covering maps are retained literally. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDifferentialScale

open MNEC.NativeAbelianDifferential NativeTranslationCover Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

def form (c : NonzeroComplexParameter.Parameter) (q : Differential X) : Differential X :=
  ⟨c.val • q.val, smul_ne_zero c.property q.property⟩

def equivalence (c : NonzeroComplexParameter.Parameter) {q : Differential X} {r : Differential Y}
    (e : MNEC.NativeDifferentialEquiv.Equiv q r) : MNEC.NativeDifferentialEquiv.Equiv (form c q) (form c r) where
  homeomorph := e.homeomorph
  differentiable := e.differentiable
  inverse_differentiable := e.inverse_differentiable
  oneForm_pullback x := by
    apply ContinuousLinearMap.ext
    intro v
    change c.val * (q.val.toFun x v) = c.val * (r.val.toFun (e.homeomorph x) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph x v))
    exact congrArg (fun L : ℂ →L[ℂ] ℂ => c.val * L v) (e.oneForm_pullback x)

def cover (c : NonzeroComplexParameter.Parameter) {q : Differential X} {r : Differential Y}
    (π : Cover q r) : Cover (form c q) (form c r) where
  map := π.map
  holomorphic := π.holomorphic
  surjective := π.surjective
  finite_fibers := π.finite_fibers
  pullback_eq := by
    exact ((Jacobians.pullbackForm π.map π.holomorphic).map_smul c.val q.val).trans
      (congrArg (fun α : Jacobians.HolomorphicOneForms Y => c.val • α) π.pullback_eq)

theorem branchValues_eq (c : NonzeroComplexParameter.Parameter) {q : Differential X} {r : Differential Y}
    (π : Cover q r) : branchValues (cover c π) = branchValues π := rfl

theorem degree_eq (c : NonzeroComplexParameter.Parameter) {q : Differential X} {r : Differential Y}
    (π : Cover q r) : NativeFullCoverDegree.degree (cover c π) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  calc
    NativeFullCoverDegree.degree (cover c π) = Nat.card ((cover c π).map ⁻¹' {x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ x.property).symm
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

end VeechDichotomy.NativeDifferentialScale
