module

public import VeechDichotomy.BeltramiMarkedRelativeCoefficients
public import VeechDichotomy.BeltramiMarkedFiberDifferential

/-! The joint analytic coefficient expressions are EXACTLY the actual
native fiber differential in the fixed sliced chart. This proves the
relative-form interpretation, including zeros and ramification, rather
than merely constructing some analytic scalar functions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRelativeFiberForm

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedCoverCoordinates BeltramiMarkedRelativeCoefficients
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

/-- The canonical unit vector in the tangent space of the complex model. -/
def unitTangent (z : ℂ) : TangentSpace 𝓘(ℂ) z :=
  (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm 1

theorem derivative_formula (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {z : ℂ} (hp : (a.val, z) ∈ domain π F hBranch s j) :
    verticalDerivative π F hBranch s j (a.val, z) =
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) _) (mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨j⟩)
        (BeltramiMarkedFiberMap.map π F hBranch a ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFiberMap.map π F hBranch a)
          ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z (unitTangent z)))) := by
  have hdom := (fiber_domain π F hBranch s j a z).mp hp
  have hi := (BeltramiMarkedFixedSlices.inverse_holomorphicAt π F hBranch s a hdom.1).mdifferentiableAt (by decide)
  have hm := (BeltramiMarkedFiberMap.holomorphic_map π F hBranch a).mdifferentiableAt (by decide)
    (x := (BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z)
  have hc' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨j⟩)
      (BeltramiMarkedFiberMap.map π F hBranch a ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z)) :=
    contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (⟨j⟩ : NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a)))
    hdom.2
  have hc := hc'.mdifferentiableAt (by decide)
  have hinner := hm.hasMFDerivAt.comp z hi.hasMFDerivAt
  have hchain := hc.hasMFDerivAt.comp z hinner
  have hder := hchain.hasFDerivAt.hasDerivAt.deriv
  rw [verticalDerivative_eq_deriv π F hBranch s j a hp]
  simpa only [ContinuousLinearMap.comp_apply, unitTangent, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel, ContinuousLinearEquiv.coe_mk, ContinuousLinearMap.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk] using! hder

theorem fiber_coefficient (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {z : ℂ} (hp : (a.val, z) ∈ domain π F hBranch s j) :
    (BeltramiMarkedFiberDifferential.form π F hBranch a).val.toFun
      ((BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z (unitTangent z)) =
        coefficient π F hBranch s j (a.val, z) := by
  let μ := BeltramiMarkedReferenceCharts.parameter A a
  let x := (BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z
  let y := BeltramiMarkedFiberMap.map π F hBranch a x
  have hdom := (fiber_domain π F hBranch s j a z).mp hp
  have hbase : (NativeBeltramiDifferential.form qX μ).val.toFun y =
      (((NativePowerCharts.chosen qX j).exponent : ℂ) *
        NativeBeltramiSurface.chart qX μ ⟨j⟩ y ^ ((NativePowerCharts.chosen qX j).exponent - 1)) •
          mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiSurface.chart qX μ ⟨j⟩) y :=
    NativeBeltramiDifferential.differential_toFun qX μ ⟨j⟩ y hdom.2
  rw [BeltramiMarkedFiberDifferential.form_value, hbase]
  change (((NativePowerCharts.chosen qX j).exponent : ℂ) *
    NativeBeltramiSurface.chart qX μ ⟨j⟩ y ^ ((NativePowerCharts.chosen qX j).exponent - 1)) *
      ((NormedSpace.fromTangentSpace (𝕜 := ℂ) _) (mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiSurface.chart qX μ ⟨j⟩) y
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFiberMap.map π F hBranch a) x
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s a).symm z (unitTangent z))))) = _
  rw [← derivative_formula π F hBranch s j a hp, coefficient,
    expression_fiber_value π F hBranch s j a hdom.1]
  rfl

end VeechDichotomy.BeltramiMarkedRelativeFiberForm
