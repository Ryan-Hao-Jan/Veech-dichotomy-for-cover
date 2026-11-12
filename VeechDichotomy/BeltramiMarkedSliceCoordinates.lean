module

public import VeechDichotomy.BeltramiMarkedUniformSlices
public import MNEC.NativeRegularTranslationAtlas

/-! The actual fixed sliced-chart coordinate is jointly continuous on
the actual scalar-extended total space. Both forward and inverse maps
are therefore available for convergent native points, without choosing
new preferred coordinates on each fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedSliceCoordinates

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
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

def source (s : ComplexBeltramiMarkParameters.Parameters A × Y) : Set (Total π F hBranch) :=
  Prod.snd ⁻¹' (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).source

theorem source_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) : IsOpen (source π F hBranch s) :=
  (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).open_source.preimage continuous_snd

def coordinate (s : ComplexBeltramiMarkParameters.Parameters A × Y) (t : Total π F hBranch) : MNEC.LatticeTorus.Plane :=
  toPlane (t.1.val * (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s t.2).2)

theorem continuousOn_coordinate (s : ComplexBeltramiMarkParameters.Parameters A × Y) :
    ContinuousOn (coordinate π F hBranch s) (source π F hBranch s) :=
  toPlane.continuous.comp_continuousOn
    ((continuous_subtype_val.comp continuous_fst).continuousOn.mul
      (((BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).continuousOn.comp
        continuous_snd.continuousOn (fun _ ht => ht)).snd))

theorem source_inclusion (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    inclusion π F hBranch p x ∈ source π F hBranch s ↔
      x ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).source := Iff.rfl

theorem coordinate_inclusion (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    coordinate π F hBranch s (inclusion π F hBranch p x) =
      toPlane (BeltramiMarkedScaledSlices.chart π F hBranch s p x) := rfl

theorem inverse_coordinate (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    (x : BeltramiMarkedFiberSurface.Surface π F hBranch p.2)
    (hx : x ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).source) :
    BeltramiMarkedUniformSlices.inverse π F hBranch s
      (p, toPlane.symm (coordinate π F hBranch s (inclusion π F hBranch p x))) = inclusion π F hBranch p x := by
  rw [coordinate_inclusion, ContinuousLinearEquiv.symm_apply_apply,
    BeltramiMarkedUniformSlices.inverse_value π F hBranch s p ((BeltramiMarkedScaledSlices.chart π F hBranch s p).map_source hx),
    (BeltramiMarkedScaledSlices.chart π F hBranch s p).left_inv hx]

theorem coordinate_tendsto {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) {t : Total π F hBranch}
    (ht : t ∈ source π F hBranch s) {f : I → Total π F hBranch} (hf : Tendsto f l (𝓝 t)) :
    Tendsto (fun i => coordinate π F hBranch s (f i)) l (𝓝 (coordinate π F hBranch s t)) :=
  ((continuousOn_coordinate π F hBranch s).continuousAt ((source_open π F hBranch s).mem_nhds ht)).tendsto.comp hf

theorem eventually_source {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) {t : Total π F hBranch}
    (ht : t ∈ source π F hBranch s) {f : I → Total π F hBranch} (hf : Tendsto f l (𝓝 t)) :
    ∀ᶠ i in l, f i ∈ source π F hBranch s := hf ((source_open π F hBranch s).mem_nhds ht)

end VeechDichotomy.BeltramiMarkedSliceCoordinates
