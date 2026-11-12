module

public import VeechDichotomy.BeltramiMarkedRegularSlices
public import VeechDichotomy.BeltramiMarkedScaledFamily

/-! Fixed primitive charts for the actual scalar-extended native family.
Their inverses use the actual scalar inverse, so a single chart family
can be used throughout a convergent sequence of nonzero scalars. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedScaledSlices

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def chart (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) :
    OpenPartialHomeomorph (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) ℂ :=
  (BeltramiMarkedFixedSlices.chart π F hBranch s p.2).transHomeomorph
    (Homeomorph.mulLeft₀ p.1.val p.1.property)

theorem chart_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    chart π F hBranch s p x = p.1.val * BeltramiMarkedFixedSlices.chart π F hBranch s p.2 x := rfl

theorem inverse_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) (z : ℂ) :
    (chart π F hBranch s p).symm z =
      (BeltramiMarkedFixedSlices.chart π F hBranch s p.2).symm (p.1.val⁻¹ * z) := rfl

theorem chart_source (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) :
    (chart π F hBranch s p).source = (BeltramiMarkedFixedSlices.chart π F hBranch s p.2).source := rfl

theorem chart_target (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) (z : ℂ) :
    z ∈ (chart π F hBranch s p).target ↔
      p.1.val⁻¹ * z ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s p.2).target := Iff.rfl

theorem derivative (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) {x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2}
    (hx : x ∈ (chart π F hBranch s p).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (chart π F hBranch s p) x ((fiberForm π F hBranch p).val.toFun x) := by
  have hd := BeltramiMarkedRegularSlices.derivative π F hBranch s hs hreg p.2 hx
  have hc : HasFDerivAt (fun z : ℂ => p.1.val * z)
      (p.1.val • ContinuousLinearMap.id ℂ ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s p.2 x) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      (hasDerivAt_const_mul p.1.val : HasDerivAt (fun z : ℂ => p.1.val * z) p.1.val _)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using!
    hc.hasMFDerivAt.comp x hd

theorem regular_source (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) : (chart π F hBranch s p).source ⊆ regularSet (fiberForm π F hBranch p) := by
  intro x hx hz
  have hz' : p.1.val • (BeltramiMarkedFiberDifferential.form π F hBranch p.2).val.toFun x = 0 := hz
  exact BeltramiMarkedRegularSlices.regular_source π F hBranch s hs hreg p.2 hx
    ((smul_eq_zero.mp hz').resolve_left p.1.property)

def primitiveChart (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2)
    (hx : x ∈ (chart π F hBranch s p).source) :
    MNEC.NativePrimitiveTransitions.PrimitiveChart (fiberForm π F hBranch p)
      ⟨x, regular_source π F hBranch s hs hreg p hx⟩ where
  chart := chart π F hBranch s p
  center := hx
  regular_source := regular_source π F hBranch s hs hreg p
  derivative := fun _ hy => derivative π F hBranch s hs hreg p hy

end VeechDichotomy.BeltramiMarkedScaledSlices
