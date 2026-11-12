module

public import VeechDichotomy.BeltramiMarkedScaledFamily
public import VeechDichotomy.BeltramiMarkedRelativeFiberForm

/-! Actual local primitives of the native fiber differential, including
at zeros and ramification. A base power-chart primitive is pulled back
through the genuine covering map and scaled by the actual fiber scalar.
No primitive or derivative identity is supplied as an oracle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedPowerPrimitives

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def basePrimitive (j : X) (μ : BeltramiPlane.Parameter) (y : NativeBeltramiSurface.Surface qX μ) : ℂ :=
  NativeBeltramiSurface.chart qX μ ⟨j⟩ y ^ (NativePowerCharts.chosen qX j).exponent

theorem base_derivative (j : X) (μ : BeltramiPlane.Parameter)
    (y : NativeBeltramiSurface.Surface qX μ)
    (hy : y ∈ (NativeBeltramiSurface.chart qX μ ⟨j⟩).source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (basePrimitive (qX := qX) j μ) y
      ((NativeBeltramiDifferential.form qX μ).val.toFun y) := by
  let c := NativeBeltramiSurface.chart qX μ ⟨j⟩
  let k := (NativePowerCharts.chosen qX j).exponent
  have hc' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (⟨j⟩ : NativeBeltramiSurface.Surface qX μ)) hy
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c y := hc'.mdifferentiableAt (by decide)
  have hp : HasDerivAt (fun z : ℂ => z ^ k) ((k : ℂ) * c y ^ (k - 1)) (c y) := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id (c y)).pow k
  have hpow : HasFDerivAt (fun z : ℂ => z ^ k)
      (((k : ℂ) * c y ^ (k - 1)) • ContinuousLinearMap.id ℂ ℂ) (c y) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hp
  have hcomp := hpow.hasMFDerivAt.comp y hc.hasMFDerivAt
  have hform : (NativeBeltramiDifferential.form qX μ).val.toFun y =
      ((k : ℂ) * c y ^ (k - 1)) • mfderiv 𝓘(ℂ) 𝓘(ℂ) c y :=
    NativeBeltramiDifferential.differential_toFun qX μ ⟨j⟩ y hy
  convert hcomp using 1
  · funext z
    rfl
  · apply ContinuousLinearMap.ext
    intro w
    exact congrArg (fun L : ℂ →L[ℂ] ℂ => L w) hform

def domain (j : X) (p : Base A) : Set (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :=
  BeltramiMarkedFiberMap.map π F hBranch p.2 ⁻¹'
    (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A p.2) ⟨j⟩).source

theorem domain_open (j : X) (p : Base A) : IsOpen (domain π F hBranch j p) :=
  (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A p.2) ⟨j⟩).open_source.preimage
    (BeltramiMarkedFiberMap.holomorphic_map π F hBranch p.2).continuous

def primitive (j : X) (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) : ℂ :=
  p.1.val * basePrimitive j (BeltramiMarkedReferenceCharts.parameter A p.2) (BeltramiMarkedFiberMap.map π F hBranch p.2 y)

theorem derivative (j : X) (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2)
    (hy : y ∈ domain π F hBranch j p) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (primitive π F hBranch j p) y ((fiberForm π F hBranch p).val.toFun y) := by
  have hb := base_derivative j (BeltramiMarkedReferenceCharts.parameter A p.2)
    (BeltramiMarkedFiberMap.map π F hBranch p.2 y) hy
  have hm := (BeltramiMarkedFiberMap.holomorphic_map π F hBranch p.2).mdifferentiableAt (by decide) (x := y)
  have hcomp := hb.comp y hm.hasMFDerivAt
  have hpull : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ)
      (fun z => basePrimitive j (BeltramiMarkedReferenceCharts.parameter A p.2) (BeltramiMarkedFiberMap.map π F hBranch p.2 z))
      y ((BeltramiMarkedFiberDifferential.form π F hBranch p.2).val.toFun y) := by
    simpa only [Function.comp_def, BeltramiMarkedFiberDifferential.form_value] using hcomp
  have hscalar : HasFDerivAt (fun z : ℂ => p.1.val * z) (p.1.val • ContinuousLinearMap.id ℂ ℂ)
      (basePrimitive j (BeltramiMarkedReferenceCharts.parameter A p.2) (BeltramiMarkedFiberMap.map π F hBranch p.2 y)) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      (hasDerivAt_const_mul p.1.val : HasDerivAt (fun z : ℂ => p.1.val * z) p.1.val _)
  simpa only [primitive, Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using!
    hscalar.hasMFDerivAt.comp y hpull

end VeechDichotomy.BeltramiMarkedPowerPrimitives
