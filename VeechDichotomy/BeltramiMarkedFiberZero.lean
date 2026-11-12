module

public import VeechDichotomy.BeltramiMarkedFiberRelocation

/-! With zero displacements, the actual native fiber is genuinely
equivalent to the native Beltrami deformation of the original covering
source. The equivalence preserves the true differential and cover map. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberZero

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
  (a : ComplexBeltramiMarkParameters.Parameters A) (hzero : ∀ i, a.val.2 i = 0)

include hzero in
theorem transport_zero : BeltramiMarkedBaseTransport.transported F a = Homeomorph.refl X := by
  let p := ComplexBeltramiMarkParameters.productHomeomorph A a
  have hδ : p.2 = fun _ => DisjointPointTransport.zeroParameter := by
    funext i
    apply Subtype.ext
    exact hzero i
  have hp : p = (p.1, fun _ => DisjointPointTransport.zeroParameter) := Prod.ext rfl hδ
  change F.map p = Homeomorph.refl X
  rw [hp]
  exact F.identity p.1

def equivalence : MNEC.NativeDifferentialEquiv.Equiv
    (BeltramiMarkedFiberDifferential.form π F hBranch a)
    (NativeBeltramiDifferential.form qY (BeltramiMarkedReferenceCharts.parameter A a)) :=
  NativeCoverIsomorphism.equivalence_of_commutes (BeltramiMarkedFiberDifferential.cover π F hBranch a)
    (NativeBeltramiCover.cover π (BeltramiMarkedReferenceCharts.parameter A a))
    (BeltramiMarkedFiberMap.toBeltramiSource π F hBranch a) (by
      intro y
      apply (NativeBeltramiSurface.toOriginal qX (BeltramiMarkedReferenceCharts.parameter A a)).injective
      change π.map y.point = BeltramiMarkedBaseTransport.transported F a (π.map y.point)
      rw [transport_zero F a hzero]
      rfl)

theorem commutes (y : BeltramiMarkedFiberSurface.Surface π F hBranch a) :
    (NativeBeltramiCover.cover π (BeltramiMarkedReferenceCharts.parameter A a)).map
      ((equivalence π F hBranch a hzero).homeomorph y) =
        (BeltramiMarkedFiberDifferential.cover π F hBranch a).map y := by
  apply (NativeBeltramiSurface.toOriginal qX (BeltramiMarkedReferenceCharts.parameter A a)).injective
  change π.map y.point = BeltramiMarkedBaseTransport.transported F a (π.map y.point)
  rw [transport_zero F a hzero]
  rfl

end VeechDichotomy.BeltramiMarkedFiberZero
