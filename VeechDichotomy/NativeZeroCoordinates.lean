module

public import VeechDichotomy.NativeSurface
public import VeechDichotomy.AnalyticPowerCoordinate
public import MNEC.NativeLocalPrimitives

/-! Genuine local power coordinates for the primitive of an arbitrary
native nonzero holomorphic differential, at any point including zeros.
The primitive cannot be locally constant by the proved identity theorem
for the given nonzero cotangent section. Its power normal form is derived.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeZeroCoordinates

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open Set Filter Metric Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem disk_primitive_not_locally_constant (q : Differential X) (b : X)
    {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z ∈ ball ((chartAt ℂ b) b) r,
      HasDerivAt f (Jacobians.NativeCanonical.coeffAt q.val b z) z) :
    ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ b) b), f z = f ((chartAt ℂ b) b) := by
  intro hconst
  have hd0 : ∀ᶠ z in 𝓝 ((chartAt ℂ b) b), deriv f z = 0 := by
    have hlocal : ∀ᶠ z in 𝓝 ((chartAt ℂ b) b),
        f =ᶠ[𝓝 z] fun _ => f ((chartAt ℂ b) b) :=
      eventually_eventually_nhds.mpr hconst
    filter_upwards [hlocal] with z hz
    have hc : HasDerivAt (fun _ : ℂ => f ((chartAt ℂ b) b)) (0 : ℂ) z :=
      hasDerivAt_const _ _
    exact (hc.congr_of_eventuallyEq hz).deriv
  have hc0 : ∀ᶠ z in 𝓝 ((chartAt ℂ b) b),
      Jacobians.NativeCanonical.coeffAt q.val b z = 0 := by
    filter_upwards [ball_mem_nhds _ hr, hd0] with z hz hd
    rw [← (hf z hz).deriv]
    exact hd
  exact q.property (Jacobians.NativeCanonical.eq_zero_of_coeffAt_eventually_zero q.val hc0)

theorem disk_primitive_derivative (q : Differential X) (b : X) {f : ℂ → ℂ}
    {y : X} (hy : y ∈ (chartAt ℂ b).source)
    (hf : HasDerivAt f (Jacobians.NativeCanonical.coeffAt q.val b ((chartAt ℂ b) y))
      ((chartAt ℂ b) y)) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z : X => f ((chartAt ℂ b) z) - f ((chartAt ℂ b) b))
      y (q.val.toFun y) := by
  let d := Jacobians.NativeCanonical.coeffAt q.val b ((chartAt ℂ b) y)
  have hDf : HasFDerivAt f (d • ContinuousLinearMap.id ℂ ℂ) ((chartAt ℂ b) y) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hf
  have hc := ((mdifferentiable_chart (I := 𝓘(ℂ)) b).mdifferentiableAt hy).hasMFDerivAt
  have hcomp := hDf.hasMFDerivAt.comp y hc
  have hmap : (d • ContinuousLinearMap.id ℂ ℂ).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ b) y) = q.val.toFun y := by
    rw [MNEC.RegularPrimitiveCharts.toFun_eq_coeffAt_smul_mfderiv q b y hy]
    rfl
  have hcomp' : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ chartAt ℂ b) y (q.val.toFun y) := by
    convert hcomp using 1
    exact hmap.symm
  have hconst : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun _ : X => f ((chartAt ℂ b) b)) y 0 :=
    hasMFDerivAt_const _ _
  simpa only [Function.comp_def, sub_zero] using! hcomp'.sub hconst

theorem exists_native_power_chart (q : Differential X) (b : X) :
    ∃ k : ℕ, 0 < k ∧ ∃ E : OpenPartialHomeomorph X ℂ,
      b ∈ E.source ∧ E b = 0 ∧
      (∀ y ∈ E.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z : X => (E z) ^ k) y (q.val.toFun y)) ∧
      (∀ y ∈ E.source, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω E y) ∧
      (∀ z ∈ E.target, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω E.symm z) := by
  obtain ⟨r, hr, _, f, hf⟩ := MNEC.NativeLocalPrimitives.exists_disk_primitive q b
  let c := chartAt ℂ b
  let a := c b
  have hfan : AnalyticAt ℂ f a :=
    ((show DifferentiableOn ℂ f (ball a r) from
      fun z hz => (hf z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball)
        a (mem_ball_self hr)
  obtain ⟨k, hk, e, hae, hea, hpow, hean, heinv⟩ :=
    AnalyticPowerCoordinate.exists_power_coordinate hfan
      (disk_primitive_not_locally_constant q b hr hf)
  let U := c.source ∩ c ⁻¹' ball a r
  have hU : IsOpen U := c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
  have hbU : b ∈ U := ⟨mem_chart_source ℂ b, mem_ball_self hr⟩
  let E₀ := c.trans e
  let E := E₀.restr U
  have hbE : b ∈ E.source := ⟨⟨mem_chart_source ℂ b, hae⟩, by rwa [hU.interior_eq]⟩
  refine ⟨k, hk, E, hbE, hea, ?_, ?_, ?_⟩
  · intro y hy
    have hyU : y ∈ U := interior_subset hy.2
    have hp := disk_primitive_derivative q b hyU.1 (hf (c y) hyU.2)
    have heq : (fun z : X => (E z) ^ k) =ᶠ[𝓝 y]
        (fun z : X => f (c z) - f a) := by
      filter_upwards [E.open_source.mem_nhds hy] with z hz
      exact (hpow (c z) hz.1.2).symm
    exact hp.congr_of_eventuallyEq heq
  · intro y hy
    change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ c) y
    exact ((hean (c y) hy.1.2).contDiffAt.contMDiffAt).comp y
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (x := b)).contMDiffAt
        ((chartAt ℂ b).open_source.mem_nhds hy.1.1))
  · intro z hz
    change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (c.symm ∘ e.symm) z
    exact ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := b)).contMDiffAt
      ((chartAt ℂ b).open_target.mem_nhds hz.1.2)).comp z
      ((heinv z hz.1.1).contDiffAt.contMDiffAt)

end VeechDichotomy.NativeZeroCoordinates
