module

public import VeechDichotomy.NativePhysicalHolomorphicMap
public import VeechDichotomy.NativeUnramifiedCover
public import VeechDichotomy.HolomorphicLocalInverse
public import Jacobians.MappingDegree.RegularValueExistsRegUnconditional

/-! A surjective holomorphic map of compact connected complex curves
pulls a nonzero holomorphic differential back to a nonzero differential.
A regular target value avoiding its finite zero set supplies the proof;
no nonzero source differential is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicSurjectivePullback

open MNEC.NativeAbelianDifferential Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

theorem pullback_ne_zero (q : Differential X) (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hsurj : Function.Surjective f) :
    Jacobians.pullbackForm f hf q.val ≠ 0 := by
  have hnc : ¬ Jacobians.Discharge.IsConstantMap f := by
    rintro ⟨x, hx⟩
    let : Nontrivial X := NativePhysicalHolomorphicMap.nontrivial q
    obtain ⟨z, hzx⟩ := exists_ne x
    obtain ⟨y, hy⟩ := hsurj z
    exact hzx (hy.symm.trans (hx y))
  have hfinite := (zeroSet_finite q).union (Jacobians.Discharge.Manifold.criticalValues_finite_general f hf hnc)
  let : Infinite X := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := hfinite.exists_notMem
  have hxReg : x ∈ regularSet q := fun h => hx (Or.inl h)
  have hxCrit : x ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f := fun h => hx (Or.inr h)
  obtain ⟨y, hy⟩ := hsurj x
  have hinj := Jacobians.Discharge.ContMDiff.Degree.preimages_locally_injective_of_notMem_criticalValues hxCrit y hy
  have hder := Jacobians.Discharge.ContMDiff.Degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood hf hnc y hinj
  intro hzero
  have hval : (q.val.toFun (f y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f y) = 0 :=
    congrArg (fun α : Jacobians.HolomorphicOneForms Y => α.toFun y) hzero
  have hbase : q.val.toFun (f y) ≠ 0 := by rw [hy]; exact hxReg
  have hline := NativeUnramifiedCover.complexLine_injective_of_ne_zero _ hbase
  have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) f y = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    apply hline
    have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L z) hval
    simpa only [ContinuousLinearMap.comp_apply, zero_apply, map_zero] using! h
  rw [HolomorphicLocalInverse.mfderiv_eq_fderiv_chart (hf.mdifferentiableAt (by decide) (x := y))] at hmf
  apply hder
  have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hmf
  simpa only [fderiv_eq_smul_deriv, one_smul, zero_apply] using h

end VeechDichotomy.HolomorphicSurjectivePullback
