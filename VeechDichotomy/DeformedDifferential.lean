module

public import VeechDichotomy.DeformedComplexAtlas
public import VeechDichotomy.CotangentGluing

/-! The actual nonvanishing analytic cotangent section dz on the deformed
regular complex surface. Its constant coefficients satisfy the transition
law by the proved complex translation germs, then generic cotangent gluing
constructs the section. No desired differential is supplied as input.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.DeformedDifferential

open MNEC.NativeAbelianDifferential DeformedRegularAtlas LinearGroup
open Set Topology
open scoped Manifold ContDiff Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (DeformedRegular q A) :=
  DeformedComplexAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (DeformedRegular q A) :=
  DeformedComplexAtlas.isComplexManifold q A ω

theorem extChartAt_eq (x : DeformedRegular q A) :
    extChartAt 𝓘(ℂ) x = (DeformedComplexAtlas.complexChart q A x).toPartialEquiv := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
  rfl

theorem extChartAt_coe (x : DeformedRegular q A) :
    (extChartAt 𝓘(ℂ) x : DeformedRegular q A → ℂ) =
      DeformedComplexAtlas.complexChart q A x :=
  congrArg (fun e : PartialEquiv (DeformedRegular q A) ℂ => (e : DeformedRegular q A → ℂ))
    (extChartAt_eq q A x)

theorem extChartAt_symm_coe (x : DeformedRegular q A) :
    ((extChartAt 𝓘(ℂ) x).symm : ℂ → DeformedRegular q A) =
      (DeformedComplexAtlas.complexChart q A x).symm :=
  congrArg (fun e : PartialEquiv (DeformedRegular q A) ℂ => (e.symm : ℂ → DeformedRegular q A))
    (extChartAt_eq q A x)

def coefficients : CotangentGluing.Coefficients (DeformedRegular q A) where
  coeff _ _ := 1
  analytic _ := analyticOnNhd_const
  cocycle x x' z hz hy := by
    have hp : z ∈ ((DeformedComplexAtlas.complexChart q A x).symm.trans
        (DeformedComplexAtlas.complexChart q A x')).source := by
      rw [extChartAt_eq] at hz
      rw [extChartAt_eq, extChartAt_eq] at hy
      exact ⟨hz, hy⟩
    obtain ⟨a, ha⟩ := DeformedComplexAtlas.transition_germ q A x x' z hp
    have hd : HasFDerivAt
        ((DeformedComplexAtlas.complexChart q A x).symm.trans
          (DeformedComplexAtlas.complexChart q A x')) (ContinuousLinearMap.id ℂ ℂ) z :=
      ((hasFDerivAt_id z).add_const a).congr_of_eventuallyEq ha
    change (1 : ℂ) = 1 * fderiv ℂ
      ((extChartAt 𝓘(ℂ) x') ∘ (extChartAt 𝓘(ℂ) x).symm) z 1
    have hfd : fderiv ℂ ((extChartAt 𝓘(ℂ) x') ∘ (extChartAt 𝓘(ℂ) x).symm) z =
        ContinuousLinearMap.id ℂ ℂ := by
      rw [extChartAt_coe, extChartAt_symm_coe]
      exact hd.fderiv
    rw [hfd, ContinuousLinearMap.id_apply, one_mul]

def differential : CotangentGluing.HolomorphicForm (DeformedRegular q A) :=
  CotangentGluing.nativeForm (coefficients q A)

theorem differential_toFun (x y : DeformedRegular q A)
    (hy : y ∈ (DeformedComplexAtlas.complexChart q A x).source) :
    (differential q A).toFun y =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (DeformedComplexAtlas.complexChart q A x) y := by
  have hyext : y ∈ (extChartAt 𝓘(ℂ) x).source := by
    simpa only [extChartAt_eq] using hy
  rw [differential, CotangentGluing.nativeForm_toFun _ x y hyext]
  change (1 : ℂ) • mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x) y = _
  rw [one_smul, extChartAt_coe]

theorem differential_coefficient (x y : DeformedRegular q A)
    (hy : y ∈ (DeformedComplexAtlas.complexChart q A x).source) :
    (differential q A).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := DeformedRegular q A)) x).symmL ℂ y 1) = 1 :=
  CotangentGluing.nativeForm_coefficient (coefficients q A) x y hy

theorem differential_nonvanishing (x : DeformedRegular q A) :
    (differential q A).toFun x ≠ 0 := by
  intro hz
  have h := differential_coefficient q A x x (DeformedRegularAtlas.chart_center q A x)
  rw [hz, zero_apply] at h
  exact zero_ne_one h

theorem hasMFDerivAt_complexChart (x y : DeformedRegular q A)
    (hy : y ∈ (DeformedComplexAtlas.complexChart q A x).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (DeformedComplexAtlas.complexChart q A x) y
      ((differential q A).toFun y) := by
  rw [differential_toFun q A x y hy]
  exact (mdifferentiableAt_atlas (I := 𝓘(ℂ)) (show
    DeformedComplexAtlas.complexChart q A x ∈ atlas ℂ (DeformedRegular q A) from ⟨x, rfl⟩) hy).hasMFDerivAt

end VeechDichotomy.DeformedDifferential
