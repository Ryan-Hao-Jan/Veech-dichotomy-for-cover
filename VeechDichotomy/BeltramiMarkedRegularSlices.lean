module

public import VeechDichotomy.BeltramiMarkedRelativeFiberForm
public import MNEC.NativePrimitiveTransitions

/-! A fixed regular total chart is a genuine primitive chart on every
fiber that it meets, whenever its fixed base center is regular. Both
the differential identity and absence of zeros on its entire source
are proved from the actual covering map. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRegularSlices

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def baseCenter (s : ComplexBeltramiMarkParameters.Parameters A × Y) : X :=
  BeltramiMarkedBaseTransport.transported F s.1 (π.map s.2)

theorem chart_value (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (a : ComplexBeltramiMarkParameters.Parameters A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch a) :
    BeltramiMarkedFixedSlices.chart π F hBranch s a x =
      NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨baseCenter π F s⟩
        (BeltramiMarkedFiberMap.map π F hBranch a x) := by
  have hs' : (⟨s⟩ : BeltramiMarkedReferenceSpace.TotalSpace A qY) ∉
      (BeltramiMarkedRelocationData.data π F hBranch).critical := hs
  change (HolomorphicCoverRelocationTransitions.rawChart (BeltramiMarkedRelocationData.data π F hBranch)
    (⟨s⟩ : BeltramiMarkedReferenceSpace.TotalSpace A qY) ⟨(a, x.point)⟩).2 = _
  rw [HolomorphicCoverRelocationTransitions.rawChart, dite_eq_right hs',
    HolomorphicCoverRelocationData.Data.regular_apply]
  rfl

theorem base_source (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (a : ComplexBeltramiMarkParameters.Parameters A)
    {x : BeltramiMarkedFiberSurface.Surface π F hBranch a}
    (hx : x ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).source) :
    BeltramiMarkedFiberMap.map π F hBranch a x ∈
      (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A a) ⟨baseCenter π F s⟩).source := by
  have hs' : (⟨s⟩ : BeltramiMarkedReferenceSpace.TotalSpace A qY) ∉
      (BeltramiMarkedRelocationData.data π F hBranch).critical := hs
  change (⟨(a, x.point)⟩ : BeltramiMarkedReferenceSpace.TotalSpace A qY) ∈
    (HolomorphicCoverRelocationTransitions.rawChart (BeltramiMarkedRelocationData.data π F hBranch) ⟨s⟩).source at hx
  rw [HolomorphicCoverRelocationTransitions.rawChart, dite_eq_right hs'] at hx
  have ht := ((BeltramiMarkedRelocationData.data π F hBranch).regular_source ⟨⟨s⟩, hs⟩ _).mp hx |>.2
  change (a, BeltramiMarkedBaseTransport.transported F a (π.map x.point)) ∈
    (BeltramiMarkedReferenceCharts.chart A qX (baseCenter π F s)).source at ht
  exact (BeltramiMarkedReferenceCharts.chart_source A qX (baseCenter π F s) _).mp ht

theorem derivative (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : baseCenter π F s ∈ regularSet qX)
    (a : ComplexBeltramiMarkParameters.Parameters A)
    {x : BeltramiMarkedFiberSurface.Surface π F hBranch a}
    (hx : x ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s a) x
      ((BeltramiMarkedFiberDifferential.form π F hBranch a).val.toFun x) := by
  let j := baseCenter π F s
  let μ := BeltramiMarkedReferenceCharts.parameter A a
  let y := BeltramiMarkedFiberMap.map π F hBranch a x
  have hy := base_source π F hBranch s hs a hx
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (NativeBeltramiSurface.chart qX μ ⟨j⟩) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (⟨j⟩ : NativeBeltramiSurface.Surface qX μ)) hy
  have hm := (BeltramiMarkedFiberMap.holomorphic_map π F hBranch a).mdifferentiableAt (by decide) (x := x)
  have hk := (NativePowerCharts.chosen qX j).regular_center_exponent_one hreg
  have hbase : (NativeBeltramiDifferential.form qX μ).val.toFun y =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (NativeBeltramiSurface.chart qX μ ⟨j⟩) y := by
    simpa only [NativeBeltramiDifferential.atlasCoefficient, NativeBeltramiCharts.powerAt, hk,
      Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] using!
        NativeBeltramiDifferential.differential_toFun qX μ ⟨j⟩ y hy
  have hd := (hc.mdifferentiableAt (by decide)).hasMFDerivAt.comp x hm.hasMFDerivAt
  rw [BeltramiMarkedFiberDifferential.form_value, hbase]
  have heq : (BeltramiMarkedFixedSlices.chart π F hBranch s a : _ → ℂ) =
      NativeBeltramiSurface.chart qX μ ⟨j⟩ ∘ BeltramiMarkedFiberMap.map π F hBranch a :=
    funext (chart_value π F hBranch s hs a)
  rw [heq]
  exact hd

theorem regular_source (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : baseCenter π F s ∈ regularSet qX)
    (a : ComplexBeltramiMarkParameters.Parameters A) :
    (BeltramiMarkedFixedSlices.chart π F hBranch s a).source ⊆
      regularSet (BeltramiMarkedFiberDifferential.form π F hBranch a) := by
  intro x hx hz
  have hd := (derivative π F hBranch s hs hreg a hx).mfderiv
  have hdiff : (BeltramiMarkedFixedSlices.chart π F hBranch s a).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨fun _ hy => (BeltramiMarkedFixedSlices.holomorphicAt π F hBranch s a hy).mdifferentiableAt (by decide) |>.mdifferentiableWithinAt,
      fun _ hy => (BeltramiMarkedFixedSlices.inverse_holomorphicAt π F hBranch s a hy).mdifferentiableAt (by decide) |>.mdifferentiableWithinAt⟩
  have hinj := (hdiff.mfderiv hx).injective
  let : Nontrivial (TangentSpace 𝓘(ℂ) x) := inferInstanceAs (Nontrivial ℂ)
  change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFixedSlices.chart π F hBranch s a) x) at hinj
  rw [hd, hz] at hinj
  exact Function.not_injective_const hinj

def primitiveChart (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : baseCenter π F s ∈ regularSet qX)
    (a : ComplexBeltramiMarkParameters.Parameters A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch a)
    (hx : x ∈ (BeltramiMarkedFixedSlices.chart π F hBranch s a).source) :
    MNEC.NativePrimitiveTransitions.PrimitiveChart (BeltramiMarkedFiberDifferential.form π F hBranch a)
      ⟨x, regular_source π F hBranch s hs hreg a hx⟩ where
  chart := BeltramiMarkedFixedSlices.chart π F hBranch s a
  center := hx
  regular_source := regular_source π F hBranch s hs hreg a
  derivative := fun _ hy => derivative π F hBranch s hs hreg a hy

end VeechDichotomy.BeltramiMarkedRegularSlices
