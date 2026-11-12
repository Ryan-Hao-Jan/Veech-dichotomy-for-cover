module

public import VeechDichotomy.BeltramiMarkedReferenceMorphisms
public import VeechDichotomy.UniformBeltramiTransportGerms
public import VeechDichotomy.NormalizedBeltramiTotalCoordinates

/-! The constructed marked transports give an actual homeomorphism of
the reference base total space, preserving ALL parameters. Its marked
inner regions are open in the total space, not only open in each fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedBaseTransport

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedReferenceSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter} {A : Data qX b μ₀} (F : Family A)

def transported (a : ComplexBeltramiMarkParameters.Parameters A) : X ≃ₜ X :=
  F.map (ComplexBeltramiMarkParameters.productHomeomorph A a)

theorem continuous_transported : Continuous (fun p : ComplexBeltramiMarkParameters.Parameters A × X => transported F p.1 p.2) :=
  Continuous.comp (f := fun p : ComplexBeltramiMarkParameters.Parameters A × X =>
      (ComplexBeltramiMarkParameters.productHomeomorph A p.1, p.2))
    (g := fun p : A.Parameters × X => F.map p.1 p.2) F.continuous_forward
    (((ComplexBeltramiMarkParameters.productHomeomorph A).continuous.comp continuous_fst).prodMk continuous_snd)

theorem continuous_transported_inverse : Continuous (fun p : ComplexBeltramiMarkParameters.Parameters A × X => (transported F p.1).symm p.2) :=
  Continuous.comp (f := fun p : ComplexBeltramiMarkParameters.Parameters A × X =>
      (ComplexBeltramiMarkParameters.productHomeomorph A p.1, p.2))
    (g := fun p : A.Parameters × X => (F.map p.1).symm p.2) F.continuous_inverse
    (((ComplexBeltramiMarkParameters.productHomeomorph A).continuous.comp continuous_fst).prodMk continuous_snd)

def homeomorph : TotalSpace A qX ≃ₜ TotalSpace A qX :=
  ((toProduct A qX).trans (ParameterizedCoverChart.homeomorph (transported F)
    (continuous_transported F) (continuous_transported_inverse F))).trans (toProduct A qX).symm

theorem homeomorph_point (z : TotalSpace A qX) :
    (homeomorph F z).point = (z.point.1, transported F z.point.1 z.point.2) := rfl

theorem inverse_point (z : TotalSpace A qX) :
    ((homeomorph F).symm z).point = (z.point.1, (transported F z.point.1).symm z.point.2) := rfl

def coordinate (i : Fin m) (z : TotalSpace A qX) : ℂ :=
  (NormalizedBeltramiTotalCoordinates.forward (A.disks i) (realization A qX z)).2

def chartSource (i : Fin m) : Set (TotalSpace A qX) :=
  {z | z.point.2 ∈ (NativePowerCharts.chosen qX (b i)).chart.source}

theorem chartSource_open (i : Fin m) : IsOpen (chartSource (A := A) i) :=
  (NativePowerCharts.chosen qX (b i)).chart.open_source.preimage
    (continuous_snd.comp (toProduct A qX).continuous)

theorem coordinate_holomorphicAt (i : Fin m) {z : TotalSpace A qX} (hz : z ∈ chartSource (A := A) i) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) 𝓘(ℂ) ω (coordinate (A := A) i) z := by
  have h := (NormalizedBeltramiTotalCoordinates.holomorphicAt (A.disks i) (realization A qX z) hz).comp z
    (realization_holomorphic A qX z)
  exact (contDiff_snd.contMDiff _).comp z h

def region (i : Fin m) : Set (TotalSpace A qX) := chartSource (A := A) i ∩ coordinate (A := A) i ⁻¹' ball (0 : ℂ) 1

theorem region_open (i : Fin m) : IsOpen (region (A := A) i) :=
  (show ContinuousOn (coordinate (A := A) i) (chartSource (A := A) i) from
    fun _ hz => (coordinate_holomorphicAt i hz).continuousAt.continuousWithinAt).isOpen_inter_preimage
      (chartSource_open i) isOpen_ball

theorem region_norm (i : Fin m) {z : TotalSpace A qX} (hz : z ∈ region (A := A) i) : ‖coordinate (A := A) i z‖ < 1 := by
  simpa only [mem_preimage, mem_ball, dist_zero_right] using hz.2

theorem center_region (a : ComplexBeltramiMarkParameters.Parameters A) (i : Fin m) :
    (⟨(a, b i)⟩ : TotalSpace A qX) ∈ region (A := A) i := by
  refine ⟨(NativePowerCharts.chosen qX (b i)).center, ?_⟩
  rw [mem_preimage, mem_ball, dist_zero_right]
  change ‖BeltramiChartNormalization.scale (A.disks i).radius *
    (NativeBeltramiCharts.chart qX (b i) (BeltramiMarkedReferenceCharts.parameter A a, b i)).2‖ < 1
  rw [NativeBeltramiCharts.chart_center_zero, mul_zero, norm_zero]
  norm_num

end VeechDichotomy.BeltramiMarkedBaseTransport
