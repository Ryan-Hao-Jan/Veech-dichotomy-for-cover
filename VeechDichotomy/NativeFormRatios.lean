module

public import VeechDichotomy.NativeSurface
public import Mathlib.Geometry.Manifold.Complex

/-! The ratio of an arbitrary native holomorphic form to a nowhere-zero
native form is a genuine global holomorphic function. Pointwise intrinsic
proportionality and local coefficient quotients are proved from the
actual cotangent trivializations, without a Riemann--Roch assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFormRatios

open MNEC.NativeAbelianDifferential Jacobians.Montel Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (η : Jacobians.HolomorphicOneForms X)

def ratio (y : X) : ℂ := localRep η y y / localRep q.val y y

theorem denominator_ne_zero (b y : X) (hy : y ∈ (chartAt ℂ b).source) (hqy : q.val.toFun y ≠ 0) :
    localRep q.val b y ≠ 0 := by
  intro hzero
  exact hqy (Jacobians.NativeCanonical.toFun_eq_zero_of_localRep_eq_zero q.val hy hzero)

theorem pointwise_smul (y : X) (hqy : q.val.toFun y ≠ 0) :
    η.toFun y = ratio q η y • q.val.toFun y := by
  have hy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  rw [toFun_eq_localRep_smul η y y hy, toFun_eq_localRep_smul q.val y y hy, smul_smul]
  rw [ratio, div_mul_cancel₀ _ (denominator_ne_zero q y y hy hqy)]

theorem local_quotient (b y : X) (hy : y ∈ (chartAt ℂ b).source) (hqy : q.val.toFun y ≠ 0) :
    ratio q η y = localRep η b y / localRep q.val b y := by
  have heq := congrArg
    (fun L => L ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) b).symmL ℂ y 1))
    (pointwise_smul q η y hqy)
  change localRep η b y = ratio q η y * localRep q.val b y at heq
  exact (eq_div_iff (denominator_ne_zero q b y hy hqy)).mpr heq.symm

theorem mdifferentiable (hno : ∀ y : X, q.val.toFun y ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ratio q η) := by
  intro b
  let c := chartAt ℂ b
  have hb : b ∈ c.source := mem_chart_source ℂ b
  have ht : c b ∈ c.target := c.map_source hb
  have hη := (Jacobians.NativeCanonical.coeffAt_analyticAt η b ht).differentiableAt
  have hq := (Jacobians.NativeCanonical.coeffAt_analyticAt q.val b ht).differentiableAt
  have hden : Jacobians.NativeCanonical.coeffAt q.val b (c b) ≠ 0 := by
    change localRep q.val b (c.symm (c b)) ≠ 0
    rw [c.left_inv hb]
    exact denominator_ne_zero q b b hb (hno b)
  have hquot := (hη.div hq hden).mdifferentiableAt
  have hchart := (mdifferentiable_chart (I := 𝓘(ℂ)) b).mdifferentiableAt hb
  apply (hquot.comp b hchart).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hb] with y hy
  change ratio q η y = Jacobians.NativeCanonical.coeffAt η b (c y) / Jacobians.NativeCanonical.coeffAt q.val b (c y)
  rw [local_quotient q η b y hy (hno y)]
  change localRep η b y / localRep q.val b y = localRep η b (c.symm (c y)) / localRep q.val b (c.symm (c y))
  rw [c.left_inv hy]

end VeechDichotomy.NativeFormRatios
