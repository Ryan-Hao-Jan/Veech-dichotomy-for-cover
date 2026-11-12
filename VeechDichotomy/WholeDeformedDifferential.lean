module

public import VeechDichotomy.WholeDeformedAtlas
public import VeechDichotomy.CotangentGluing

/-! The actual holomorphic differential on the whole SL2-deformed compact
curve. Its coefficients k*z^(k-1) are derived from the constructed power
charts; the cocycle law follows by differentiating the proved primitive
difference identities. Its zero set is exactly the original zero set.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.WholeDeformedDifferential

open MNEC.NativeAbelianDifferential WholeDeformedAtlas LinearGroup Set Topology
open scoped Manifold ContDiff Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

def atlasCoefficient (i : WholeSurface q A) (z : ℂ) : ℂ :=
  ((powerAt q i.point).exponent : ℂ) * z ^ ((powerAt q i.point).exponent - 1)

theorem coefficient_cocycle (i j : WholeSurface q A) (z : ℂ)
    (hz : z ∈ ((chart q A i).symm.trans (chart q A j)).source) :
    atlasCoefficient q A i z =
      atlasCoefficient q A j (((chart q A i).symm.trans (chart q A j)) z) *
        fderiv ℂ ((chart q A i).symm.trans (chart q A j)) z 1 := by
  let T := (chart q A i).symm.trans (chart q A j)
  obtain ⟨c, hc⟩ := transition_power_germ q A i j z hz
  have heq : (fun w : ℂ => T w ^ (powerAt q j.point).exponent) =ᶠ[𝓝 z]
      (fun w => w ^ (powerAt q i.point).exponent + c) := hc
  have hT : HasDerivAt T (deriv T z) z := (transition_analyticAt q A i j z hz).differentiableAt.hasDerivAt
  have hleft : HasDerivAt (fun w : ℂ => T w ^ (powerAt q j.point).exponent)
      (atlasCoefficient q A j (T z) * deriv T z) z := by
    simpa only [atlasCoefficient] using! hT.pow (powerAt q j.point).exponent
  have hpoly : HasDerivAt (fun w : ℂ => w ^ (powerAt q i.point).exponent)
      (atlasCoefficient q A i z) z := by
    simpa only [atlasCoefficient, id_eq, mul_one] using!
      (hasDerivAt_id z).pow (powerAt q i.point).exponent
  have hright : HasDerivAt (fun w : ℂ => T w ^ (powerAt q j.point).exponent)
      (atlasCoefficient q A i z) z := (hpoly.add_const c).congr_of_eventuallyEq heq
  have h := hleft.unique hright
  rw [fderiv_apply_one_eq_deriv]
  exact h.symm

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

theorem extChartAt_eq (x : WholeSurface q A) :
    extChartAt 𝓘(ℂ) x = (chart q A x).toPartialEquiv := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
  rfl

theorem extChartAt_coe (x : WholeSurface q A) :
    (extChartAt 𝓘(ℂ) x : WholeSurface q A → ℂ) = chart q A x :=
  congrArg (fun e : PartialEquiv (WholeSurface q A) ℂ => (e : WholeSurface q A → ℂ))
    (extChartAt_eq q A x)

theorem extChartAt_symm_coe (x : WholeSurface q A) :
    ((extChartAt 𝓘(ℂ) x).symm : ℂ → WholeSurface q A) = (chart q A x).symm :=
  congrArg (fun e : PartialEquiv (WholeSurface q A) ℂ => (e.symm : ℂ → WholeSurface q A))
    (extChartAt_eq q A x)

def coefficients : CotangentGluing.Coefficients (WholeSurface q A) where
  coeff := atlasCoefficient q A
  analytic i := by
    intro z _
    exact analyticAt_const.mul (analyticAt_id.pow ((powerAt q i.point).exponent - 1))
  cocycle i j z hz hy := by
    rw [extChartAt_eq] at hz
    rw [extChartAt_eq, extChartAt_eq] at hy
    have hp : z ∈ ((chart q A i).symm.trans (chart q A j)).source := ⟨hz, hy⟩
    rw [extChartAt_coe, extChartAt_symm_coe]
    exact coefficient_cocycle q A i j z hp

def differential : Jacobians.HolomorphicOneForms (WholeSurface q A) :=
  CotangentGluing.nativeForm (coefficients q A)

theorem differential_toFun (i y : WholeSurface q A) (hy : y ∈ (chart q A i).source) :
    (differential q A).toFun y = atlasCoefficient q A i (chart q A i y) •
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chart q A i) y := by
  have hyext : y ∈ (extChartAt 𝓘(ℂ) i).source := by rw [extChartAt_eq]; exact hy
  rw [differential, CotangentGluing.nativeForm_toFun _ i y hyext]
  change atlasCoefficient q A i ((extChartAt 𝓘(ℂ) i) y) •
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) i) y = _
  rw [extChartAt_coe]

theorem chartPower_hasMFDerivAt (i y : WholeSurface q A) (hy : y ∈ (chart q A i).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z => chart q A i z ^ (powerAt q i.point).exponent) y
      ((differential q A).toFun y) := by
  have hp : HasDerivAt (fun z : ℂ => z ^ (powerAt q i.point).exponent)
      (atlasCoefficient q A i (chart q A i y)) (chart q A i y) := by
    simpa only [atlasCoefficient, id_eq, mul_one] using!
      (hasDerivAt_id (chart q A i y)).pow (powerAt q i.point).exponent
  have hpf : HasFDerivAt (fun z : ℂ => z ^ (powerAt q i.point).exponent)
      (atlasCoefficient q A i (chart q A i y) • ContinuousLinearMap.id ℂ ℂ) (chart q A i y) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hp
  have hc := (mdifferentiableAt_atlas (I := 𝓘(ℂ))
    (show chart q A i ∈ atlas ℂ (WholeSurface q A) from ⟨i, rfl⟩) hy).hasMFDerivAt
  have hcomp := hpf.hasMFDerivAt.comp y hc
  rw [differential_toFun q A i y hy]
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using! hcomp

/-- The form's primitive is the ACTUAL A-image of the original native
primitive, including on charts centered at a zero. -/
theorem affine_primitive_hasMFDerivAt (i y : WholeSurface q A) (hy : y ∈ (chart q A i).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ)
      (fun z : WholeSurface q A => SL2PowerLift.complexAction A
        ((powerAt q i.point).chart z.point ^ (powerAt q i.point).exponent)) y
      ((differential q A).toFun y) := by
  have heq : (fun z : WholeSurface q A => SL2PowerLift.complexAction A
        ((powerAt q i.point).chart z.point ^ (powerAt q i.point).exponent)) =
      fun z => chart q A i z ^ (powerAt q i.point).exponent :=
    funext (fun z => (chart_power q A i z).symm)
  rw [heq]
  exact chartPower_hasMFDerivAt q A i y hy

theorem localRep_eq (i y : WholeSurface q A) (hy : y ∈ (chart q A i).source) :
    Jacobians.Montel.localRep (differential q A) i y =
      atlasCoefficient q A i (chart q A i y) := by
  have h := CotangentGluing.nativeForm_coefficient (coefficients q A) i y hy
  simpa only [differential, coefficients, extChartAt_coe, Jacobians.Montel.localRep] using! h

theorem self_localRep_zero_iff (x : WholeSurface q A) :
    Jacobians.Montel.localRep (differential q A) x x = 0 ↔ x.point ∈ zeroSet q := by
  rw [localRep_eq q A x x (chart_center q A x), chart_center_zero]
  rw [(powerAt q x.point).zero_at_center_iff_one_lt]
  by_cases hk1 : (powerAt q x.point).exponent = 1
  · simp [atlasCoefficient, hk1]
  · have hkgt : 1 < (powerAt q x.point).exponent :=
      lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (powerAt q x.point).exponent_pos.ne') (Ne.symm hk1)
    simp only [atlasCoefficient, zero_pow (Nat.sub_ne_zero_of_lt hkgt), mul_zero,
      true_iff]
    exact hkgt

theorem pointwise_zero_iff (x : WholeSurface q A) :
    (differential q A).toFun x = 0 ↔ x.point ∈ zeroSet q := by
  constructor
  · intro h
    exact (self_localRep_zero_iff q A x).mp
      (Jacobians.NativeCanonical.localRep_eq_zero_of_toFun_eq_zero (differential q A) x h)
  · intro h
    exact Jacobians.NativeCanonical.toFun_eq_zero_of_localRep_eq_zero (differential q A)
      (mem_chart_source ℂ x) ((self_localRep_zero_iff q A x).mpr h)

theorem differential_ne_zero : differential q A ≠ 0 := by
  obtain ⟨b, hb⟩ := regularSet_nonempty q
  let x : WholeSurface q A := ⟨b⟩
  intro hz
  have hx0 : (differential q A).toFun x = 0 := by rw [hz]; rfl
  exact hb ((pointwise_zero_iff q A x).mp hx0)

def form : Differential (WholeSurface q A) := ⟨differential q A, differential_ne_zero q A⟩

theorem zeroSet_form : zeroSet (form q A) = WholeSurface.point ⁻¹' zeroSet q := by
  ext x
  exact pointwise_zero_iff q A x

theorem regularSet_form : regularSet (form q A) = WholeSurface.point ⁻¹' regularSet q := by
  rw [regularSet, zeroSet_form]
  rfl

end VeechDichotomy.WholeDeformedDifferential
