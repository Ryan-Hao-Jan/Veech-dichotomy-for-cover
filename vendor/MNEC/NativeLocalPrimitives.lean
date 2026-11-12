module

public import MNEC.NativePrimitiveTransitions

@[expose] public section
noncomputable section

namespace MNEC.NativeLocalPrimitives

open NativeAbelianDifferential Set Filter Metric
open scoped Manifold ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A holomorphic disk primitive exists at EVERY original point, including
zeros. No nonvanishing coefficient or inverse-function premise is needed. -/
theorem exists_disk_primitive (q : Differential X) (b : X) :
    ∃ r : ℝ, 0 < r ∧ ball ((chartAt ℂ b) b) r ⊆ (chartAt ℂ b).target ∧
      ∃ f : ℂ → ℂ, ∀ z ∈ ball ((chartAt ℂ b) b) r,
        HasDerivAt f (Jacobians.NativeCanonical.coeffAt q.val b z) z := by
  let a := (chartAt ℂ b) b
  let c := Jacobians.NativeCanonical.coeffAt q.val b
  have ha : a ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  obtain ⟨r, hr, htarget⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ b).open_target.mem_nhds ha)
  have hcder : DifferentiableOn ℂ c (ball a r) := fun z hz =>
    (Jacobians.NativeCanonical.coeffAt_analyticAt q.val b (htarget hz)).differentiableWithinAt
  obtain ⟨f, hf⟩ := (convex_ball a r).exists_forall_hasDerivWithinAt hcder
  exact ⟨r, hr, htarget, f, fun z hz => (hf z hz).hasDerivAt (isOpen_ball.mem_nhds hz)⟩

/-- A normalized actual primitive FUNCTION on an open original neighborhood.
Its native cotangent derivative is the given section also at zeros. -/
theorem exists_local_primitive_function (q : Differential X) (b : X) :
    ∃ U : Set X, IsOpen U ∧ b ∈ U ∧ ∃ F : X → ℂ, F b = 0 ∧
      (∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y)) ∧ ContinuousOn F U := by
  obtain ⟨r, hr, htarget, f, hf⟩ := exists_disk_primitive q b
  let c := chartAt ℂ b
  let a := c b
  let U := c.source ∩ c ⁻¹' ball a r
  let F : X → ℂ := fun y => f (c y) - f a
  have hU : IsOpen U := c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
  have hb : b ∈ U := ⟨mem_chart_source ℂ b, mem_ball_self hr⟩
  have hder : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y) := by
    intro y hy
    let d := Jacobians.NativeCanonical.coeffAt q.val b (c y)
    have hDf : HasFDerivAt f (d • ContinuousLinearMap.id ℂ ℂ) (c y) := by
      apply hasFDerivAt_iff_hasDerivAt.mpr
      simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hf (c y) hy.2
    have hchart := ((mdifferentiable_chart (I := 𝓘(ℂ)) b).mdifferentiableAt hy.1).hasMFDerivAt
    have hcomp := hDf.hasMFDerivAt.comp y hchart
    have hmap : (d • ContinuousLinearMap.id ℂ ℂ).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ b) y) = q.val.toFun y := by
      rw [RegularPrimitiveCharts.toFun_eq_coeffAt_smul_mfderiv q b y hy.1]
      rfl
    have hcomp' : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ c) y (q.val.toFun y) := by
      convert hcomp using 1
      exact hmap.symm
    have hconst : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun _ : X => f a) y 0 := hasMFDerivAt_const _ _
    simpa only [Function.comp_def, sub_zero] using! hcomp'.sub hconst
  exact ⟨U, hU, hb, F, by simp only [F, a, sub_self], hder,
    fun y hy => (hder y hy).mdifferentiableAt.continuousAt.continuousWithinAt⟩

/-- Equal native derivatives imply a local constant difference for arbitrary
functions on open original neighborhoods. Neither function is assumed an OPH. -/
theorem difference_germ (q : Differential X) (F G : X → ℂ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (hG : ∀ y ∈ V, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) G y (q.val.toFun y))
    (b : X) (hb : b ∈ U ∩ V) :
    ∀ᶠ y in 𝓝 b, G y = F y + (G b - F b) := by
  let c := chartAt ℂ b
  let W := c.target ∩ c.symm ⁻¹' (U ∩ V)
  let a := c b
  have hcb : b ∈ c.source := mem_chart_source ℂ b
  have hW : IsOpen W := c.symm.continuousOn.isOpen_inter_preimage c.open_target (hU.inter hV)
  have haW : a ∈ W := ⟨c.map_source hcb, by change c.symm (c b) ∈ U ∩ V; rw [c.left_inv hcb]; exact hb⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW a haW
  let h : ℂ → ℂ := fun z => G (c.symm z) - F (c.symm z)
  have hder : ∀ z ∈ ball a r, HasFDerivAt h (0 : ℂ →L[ℂ] ℂ) z := by
    intro z hz
    have hzW := hball hz
    have hsub := (hG _ hzW.2.2).sub (hF _ hzW.2.1)
    have hcInv := (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ b) hzW.1).hasMFDerivAt
    have hcomp := hsub.comp z hcInv
    have hzero : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) h z (0 : ℂ →L[ℂ] ℂ) := by
      simpa only [Function.comp_def, sub_self, ContinuousLinearMap.zero_comp] using! hcomp
    exact hzero.hasFDerivAt
  have hconstant : ∀ z ∈ ball a r, h z = h a := by
    intro z hz
    apply (convex_ball a r).is_const_of_fderivWithin_eq_zero
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt) _ hz (mem_ball_self hr)
    intro u hu
    rw [fderivWithin_of_isOpen isOpen_ball hu]
    exact (hder u hu).fderiv
  have hcCont : ContinuousAt c b := c.continuousOn.continuousAt (c.open_source.mem_nhds hcb)
  have hnear : ∀ᶠ y in 𝓝 b, y ∈ c.source ∧ c y ∈ ball a r := by
    filter_upwards [c.open_source.mem_nhds hcb, hcCont (isOpen_ball.mem_nhds (mem_ball_self hr))] with y hy hyB
    exact ⟨hy, hyB⟩
  filter_upwards [hnear] with y hy
  have hvalue := hconstant (c y) hy.2
  change G (c.symm (c y)) - F (c.symm (c y)) = G (c.symm (c b)) - F (c.symm (c b)) at hvalue
  rw [c.left_inv hy.1, c.left_inv hcb] at hvalue
  calc
    G y = (G y - F y) + F y := by abel
    _ = (G b - F b) + F y := by rw [hvalue]
    _ = F y + (G b - F b) := add_comm _ _

end MNEC.NativeLocalPrimitives

