module

public import VeechDichotomy.ComplexBeltramiMarkParameters
public import VeechDichotomy.UniformBeltramiMarkTransport

/-! Actual displacement coordinates of varying marked tuples in the
uniform Beltrami disks. Joint continuity is derived from the fixed old
chart and the actual parameter-dependent plane lift. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiConfigurationCoordinates

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

def coordinate (i : Fin m) (p : Parameter × (Fin m → X)) : ℂ :=
  BeltramiChartNormalization.plane q (b i) (A.disks i).radius (A.disks i).radius_pos p.1
    ((NativePowerCharts.chosen q (b i)).chart (p.2 i))

theorem coordinate_continuousAt (i : Fin m) {p : Parameter × (Fin m → X)}
    (hp : p.2 i ∈ (NativePowerCharts.chosen q (b i)).chart.source) : ContinuousAt (coordinate A i) p := by
  have heval : ContinuousAt (fun z : Parameter × (Fin m → X) => z.2 i) p :=
    ((continuous_apply i).comp continuous_snd).continuousAt
  have hchart : ContinuousAt (fun z : Parameter × (Fin m → X) =>
      (NativePowerCharts.chosen q (b i)).chart (z.2 i)) p :=
    ContinuousAt.comp (f := fun z : Parameter × (Fin m → X) => z.2 i)
      (g := (NativePowerCharts.chosen q (b i)).chart)
      ((NativePowerCharts.chosen q (b i)).chart.continuousAt hp) heval
  exact ContinuousAt.comp
    (f := fun z : Parameter × (Fin m → X) => (z.1, (NativePowerCharts.chosen q (b i)).chart (z.2 i)))
    (g := fun z : Parameter × ℂ => BeltramiChartNormalization.plane q (b i)
      (A.disks i).radius (A.disks i).radius_pos z.1 z.2)
    (BeltramiChartNormalization.continuous_plane q (b i) (A.disks i).radius (A.disks i).radius_pos).continuousAt
    (continuousAt_fst.prodMk hchart)

theorem coordinate_center (μ : Parameter) (i : Fin m) : coordinate A i (μ, b) = 0 := by
  rw [coordinate, (NativePowerCharts.chosen q (b i)).center_zero, BeltramiChartNormalization.plane_zero]

def Valid (μ : Parameter) (u : Fin m → X) : Prop := μ ∈ A.baseNeighborhood ∧
  ∀ i, u i ∈ (NativePowerCharts.chosen q (b i)).chart.source ∧ ‖coordinate A i (μ, u)‖ < 1 / 2

theorem reference_valid : Valid A μ₀ b := by
  refine ⟨A.reference_mem, fun i => ⟨(NativePowerCharts.chosen q (b i)).center, ?_⟩⟩
  rw [coordinate_center, norm_zero]
  norm_num

def parameters (μ : Parameter) (u : Fin m → X) (h : Valid A μ u) : ComplexBeltramiMarkParameters.Parameters A :=
  ⟨(μ.val, fun i => coordinate A i (μ, u)), μ.property, h.1, fun i => (h.2 i).2⟩

def tuple (F : Family A) (a : ComplexBeltramiMarkParameters.Parameters A) : Fin m → X :=
  fun i => F.map (ComplexBeltramiMarkParameters.productHomeomorph A a) (b i)

theorem parameters_moves (F : Family A) (μ : Parameter) (u : Fin m → X) (h : Valid A μ u) :
    tuple A F (parameters A μ u h) = u := by
  funext i
  let p := ComplexBeltramiMarkParameters.productHomeomorph A (parameters A μ u h)
  let x : NativeBeltramiSurface.Surface q p.1.val := ⟨u i⟩
  have hx : x ∈ (F.disks p.1 i).chart.source := (h.2 i).1
  have hc : (F.disks p.1 i).chart x = (p.2 i).val := rfl
  have hm : F.map p (b i) = ((F.disks p.1 i).chart.symm (p.2 i).val).point :=
    congrArg NativeBeltramiSurface.Surface.point (F.moves p i)
  change F.map p (b i) = u i
  rw [hm, ← hc]
  exact congrArg NativeBeltramiSurface.Surface.point ((F.disks p.1 i).chart.left_inv hx)

theorem tuple_distinct (F : Family A) (a : ComplexBeltramiMarkParameters.Parameters A) : Function.Injective (tuple A F a) :=
  (F.map (ComplexBeltramiMarkParameters.productHomeomorph A a)).injective.comp A.injective

end VeechDichotomy.UniformBeltramiConfigurationCoordinates
