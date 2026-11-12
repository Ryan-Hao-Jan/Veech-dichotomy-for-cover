module

public import VeechDichotomy.BeltramiMarkedUniformSlices
public import VeechDichotomy.BeltramiMarkedFiberZero

/-! At a zero-displacement limit, every actual regular point admits the
fixed persistent flat charts constructed above. The required base
regularity is derived from the native form and the true cover, rather
than being an extra compactness or flat-limit assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedLimitFlatCharts

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

theorem base_regular (a : ComplexBeltramiMarkParameters.Parameters A) (hzero : ∀ i, a.val.2 i = 0)
    {y : Y} (hy : y ∈ regularSet qY) : BeltramiMarkedRegularSlices.baseCenter π F (a, y) ∈ regularSet qX := by
  rw [BeltramiMarkedRegularSlices.baseCenter, BeltramiMarkedFiberZero.transport_zero F a hzero]
  exact regular_maps_to_regular π hy

theorem original_regular (p : Base A) (hzero : ∀ i, p.2.val.2 i = 0)
    {x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2} (hx : x ∈ regularSet (fiberForm π F hBranch p)) :
    x.point ∈ regularSet qY := by
  have hu : x ∈ regularSet (BeltramiMarkedFiberDifferential.form π F hBranch p.2) := by
    intro hz
    apply hx
    change p.1.val • (BeltramiMarkedFiberDifferential.form π F hBranch p.2).val.toFun x = 0
    apply ContinuousLinearMap.ext
    intro v
    change p.1.val * ((BeltramiMarkedFiberDifferential.form π F hBranch p.2).val.toFun x v) = 0
    rw [hz, zero_apply, mul_zero]
  have hb := MNEC.NativeDifferentialEquiv.maps_regular (BeltramiMarkedFiberZero.equivalence π F hBranch p.2 hzero) x hu
  intro hz
  apply hb
  exact (NativeBeltramiDifferential.pointwise_zero_iff qY (BeltramiMarkedReferenceCharts.parameter A p.2)
    ((BeltramiMarkedFiberZero.equivalence π F hBranch p.2 hzero).homeomorph x)).mpr hz

theorem center (p : Base A) (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    x ∈ (BeltramiMarkedScaledSlices.chart π F hBranch (p.2, x.point) p).source :=
  BeltramiMarkedFiberCharts.chart_center π F hBranch p.2 x.point

def primitiveChart (p : Base A) (hzero : ∀ i, p.2.val.2 i = 0)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) (hx : x ∈ regularSet (fiberForm π F hBranch p)) :
    MNEC.NativePrimitiveTransitions.PrimitiveChart (fiberForm π F hBranch p) ⟨x, hx⟩ := by
  have hy := original_regular π F hBranch p hzero hx
  have hs : x.point ∉ criticalSet π := fun hc => hy (critical_subset_zeroSet π hc)
  exact BeltramiMarkedScaledSlices.primitiveChart π F hBranch (p.2, x.point) hs
    (base_regular π F p.2 hzero hy) p x (center π F hBranch p x)

theorem compact_persistence (p : Base A) (hzero : ∀ i, p.2.val.2 i = 0)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) (hx : x ∈ regularSet (fiberForm π F hBranch p))
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ (primitiveChart π F hBranch p hzero x hx).chart.target) :
    ∃ U : Set (Base A), IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch (p.2, x.point) q).target :=
  BeltramiMarkedUniformSlices.compact_persistence π F hBranch (p.2, x.point) p hK hsub

end VeechDichotomy.BeltramiMarkedLimitFlatCharts
