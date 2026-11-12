module

public import VeechDichotomy.NativeBeltramiSurface
public import VeechDichotomy.CotangentGluing

/-! The actual nonzero holomorphic differential on every native unit-disk
fiber. Its polynomial coefficients are derived from the primitive-power
identities. The zero set is exactly the original native zero set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiDifferential

open MNEC.NativeAbelianDifferential BeltramiPlane NativeBeltramiSurface NativeBeltramiCharts Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (μ : Parameter)

def atlasCoefficient (i : Surface q μ) (z : ℂ) : ℂ :=
  ((powerAt q i.point).exponent : ℂ) * z ^ ((powerAt q i.point).exponent - 1)

theorem coefficient_cocycle (i j : Surface q μ) (z : ℂ)
    (hz : z ∈ ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)).source) :
    atlasCoefficient q μ i z = atlasCoefficient q μ j
      (((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)) z) *
        fderiv ℂ ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)) z 1 := by
  let T := (NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)
  obtain ⟨c, hc⟩ := NativeBeltramiSurface.transition_power_germ q μ i j z hz
  have hT : HasDerivAt T (deriv T z) z :=
    ((NativeBeltramiSurface.transition_contDiffAt q μ i j z hz).differentiableAt (by decide)).hasDerivAt
  have hleft : HasDerivAt (fun w : ℂ => T w ^ (powerAt q j.point).exponent)
      (atlasCoefficient q μ j (T z) * deriv T z) z := by
    simpa only [atlasCoefficient] using! hT.pow (powerAt q j.point).exponent
  have hpoly : HasDerivAt (fun w : ℂ => w ^ (powerAt q i.point).exponent) (atlasCoefficient q μ i z) z := by
    simpa only [atlasCoefficient, id_eq, mul_one] using! (hasDerivAt_id z).pow (powerAt q i.point).exponent
  have hright : HasDerivAt (fun w : ℂ => T w ^ (powerAt q j.point).exponent) (atlasCoefficient q μ i z) z :=
    (hpoly.add_const c).congr_of_eventuallyEq hc
  rw [fderiv_apply_one_eq_deriv]
  exact (hleft.unique hright).symm

theorem extChartAt_eq (i : Surface q μ) :
    extChartAt 𝓘(ℂ) i = (NativeBeltramiSurface.chart q μ i).toPartialEquiv := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]
  rfl

theorem extChartAt_coe (i : Surface q μ) : (extChartAt 𝓘(ℂ) i : Surface q μ → ℂ) = NativeBeltramiSurface.chart q μ i :=
  congrArg (fun e : PartialEquiv (Surface q μ) ℂ => (e : Surface q μ → ℂ)) (extChartAt_eq q μ i)

theorem extChartAt_symm_coe (i : Surface q μ) : ((extChartAt 𝓘(ℂ) i).symm : ℂ → Surface q μ) =
    (NativeBeltramiSurface.chart q μ i).symm :=
  congrArg (fun e : PartialEquiv (Surface q μ) ℂ => (e.symm : ℂ → Surface q μ)) (extChartAt_eq q μ i)

def coefficients : CotangentGluing.Coefficients (Surface q μ) where
  coeff := atlasCoefficient q μ
  analytic i := fun _ _ => analyticAt_const.mul (analyticAt_id.pow ((powerAt q i.point).exponent - 1))
  cocycle i j z hz hy := by
    rw [extChartAt_eq] at hz
    rw [extChartAt_eq, extChartAt_eq] at hy
    have hp : z ∈ ((NativeBeltramiSurface.chart q μ i).symm.trans (NativeBeltramiSurface.chart q μ j)).source := ⟨hz, hy⟩
    rw [extChartAt_coe, extChartAt_symm_coe]
    exact coefficient_cocycle q μ i j z hp

def differential : Jacobians.HolomorphicOneForms (Surface q μ) := CotangentGluing.nativeForm (coefficients q μ)

theorem differential_toFun (i y : Surface q μ) (hy : y ∈ (NativeBeltramiSurface.chart q μ i).source) :
    (differential q μ).toFun y = atlasCoefficient q μ i (NativeBeltramiSurface.chart q μ i y) •
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiSurface.chart q μ i) y := by
  have hyext : y ∈ (extChartAt 𝓘(ℂ) i).source := by rw [extChartAt_eq]; exact hy
  rw [differential, CotangentGluing.nativeForm_toFun _ i y hyext]
  change atlasCoefficient q μ i ((extChartAt 𝓘(ℂ) i) y) • mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) i) y = _
  rw [extChartAt_coe]

theorem localRep_eq (i y : Surface q μ) (hy : y ∈ (NativeBeltramiSurface.chart q μ i).source) :
    Jacobians.Montel.localRep (differential q μ) i y = atlasCoefficient q μ i (NativeBeltramiSurface.chart q μ i y) := by
  have h := CotangentGluing.nativeForm_coefficient (coefficients q μ) i y hy
  simpa only [differential, coefficients, extChartAt_coe, Jacobians.Montel.localRep] using! h

theorem self_localRep_zero_iff (x : Surface q μ) :
    Jacobians.Montel.localRep (differential q μ) x x = 0 ↔ x.point ∈ zeroSet q := by
  rw [localRep_eq q μ x x (NativeBeltramiSurface.chart_center q μ x), NativeBeltramiSurface.chart_center_zero]
  rw [(powerAt q x.point).zero_at_center_iff_one_lt]
  by_cases hk1 : (powerAt q x.point).exponent = 1
  · simp [atlasCoefficient, hk1]
  · have hkgt : 1 < (powerAt q x.point).exponent :=
      lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (powerAt q x.point).exponent_pos.ne') (Ne.symm hk1)
    simp only [atlasCoefficient, zero_pow (Nat.sub_ne_zero_of_lt hkgt), mul_zero, true_iff]
    exact hkgt

theorem pointwise_zero_iff (x : Surface q μ) : (differential q μ).toFun x = 0 ↔ x.point ∈ zeroSet q := by
  constructor
  · intro h
    exact (self_localRep_zero_iff q μ x).mp
      (Jacobians.NativeCanonical.localRep_eq_zero_of_toFun_eq_zero (differential q μ) x h)
  · intro h
    exact Jacobians.NativeCanonical.toFun_eq_zero_of_localRep_eq_zero (differential q μ)
      (mem_chart_source ℂ x) ((self_localRep_zero_iff q μ x).mpr h)

theorem differential_ne_zero : differential q μ ≠ 0 := by
  obtain ⟨b, hb⟩ := regularSet_nonempty q
  let x : Surface q μ := ⟨b⟩
  intro hz
  have hx : (differential q μ).toFun x = 0 := by rw [hz]; rfl
  exact hb ((pointwise_zero_iff q μ x).mp hx)

def form : Differential (Surface q μ) := ⟨differential q μ, differential_ne_zero q μ⟩

theorem zeroSet_form : zeroSet (form q μ) = Surface.point ⁻¹' zeroSet q := by
  ext x
  exact pointwise_zero_iff q μ x

end VeechDichotomy.NativeBeltramiDifferential
