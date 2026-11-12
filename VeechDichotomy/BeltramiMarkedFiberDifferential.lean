module

public import VeechDichotomy.BeltramiMarkedFiberMap
public import VeechDichotomy.HolomorphicSurjectivePullback

/-! The actual nonzero holomorphic differential on every constructed
native moved fiber is the literal pullback of its native Beltrami base
differential. This supplies genuine finite native translation covers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberDifferential

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedFiberSurface
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (a : ComplexBeltramiMarkParameters.Parameters A)

def form : Differential (Surface π F hBranch a) :=
  ⟨Jacobians.pullbackForm (BeltramiMarkedFiberMap.map π F hBranch a)
    (BeltramiMarkedFiberMap.holomorphic_map π F hBranch a)
    (NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A a)).val,
   HolomorphicSurjectivePullback.pullback_ne_zero
    (NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A a))
    (BeltramiMarkedFiberMap.map π F hBranch a)
    (BeltramiMarkedFiberMap.holomorphic_map π F hBranch a)
    (BeltramiMarkedFiberMap.surjective_map π F hBranch a)⟩

def cover : Cover (NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A a)) (form π F hBranch a) where
  map := BeltramiMarkedFiberMap.map π F hBranch a
  holomorphic := BeltramiMarkedFiberMap.holomorphic_map π F hBranch a
  surjective := BeltramiMarkedFiberMap.surjective_map π F hBranch a
  finite_fibers := BeltramiMarkedFiberMap.finite_fibers π F hBranch a
  pullback_eq := rfl

theorem form_value (y : Surface π F hBranch a) : (form π F hBranch a).val.toFun y =
    ((NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A a)).val.toFun
      (BeltramiMarkedFiberMap.map π F hBranch a y)).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (BeltramiMarkedFiberMap.map π F hBranch a) y) := rfl

theorem cover_map_value (y : Y) :
    (cover π F hBranch a).map ((toOriginal π F hBranch a).symm y) =
      (⟨BeltramiMarkedBaseTransport.transported F a (π.map y)⟩ :
        NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a)) := rfl

end VeechDichotomy.BeltramiMarkedFiberDifferential
