module

public import MNEC.RegularCoordinateArea
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Perfect

/-! Positive open mass from actual physical chart area, and density of the
regular part of a connected Hausdorff slit surface. The generic chart-area
identity is instantiated separately with the proved physical measures;
no support or density hypothesis is supplied to those actual instances. -/

noncomputable section
@[expose] public section

namespace MNEC.ChartAreaSupport

open LatticeTorus SlitConnectedSum RegularPoints RegularChartedSpace MeasureTheory Set Topology
open scoped Classical

theorem isOpenPosMeasure_of_chart_area {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (e : ι → OpenPartialHomeomorph Plane X)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).target)
    (harea : ∀ i (V : Set Plane), MeasurableSet V → V ⊆ (e i).source → μ (e i '' V) = volume V) :
    Measure.IsOpenPosMeasure μ := by
  constructor
  intro U hU hne hzero
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hxi⟩ := hcover x
  let V := (e i).source ∩ e i ⁻¹' U
  have hV : IsOpen V := (e i).continuousOn.isOpen_inter_preimage (e i).open_source hU
  have hVne : V.Nonempty := ⟨(e i).symm x, (e i).map_target hxi, by
    change e i ((e i).symm x) ∈ U
    rwa [(e i).right_inv hxi]⟩
  have hvol : volume V ≠ 0 := hV.measure_ne_zero volume hVne
  apply hvol
  rw [← harea i V hV.measurableSet inter_subset_left]
  apply measure_mono_null _ hzero
  rintro _ ⟨p, hp, rfl⟩
  exact hp.2

theorem surfaceNontrivial (L₁ L₂ : Lattice) (w : Plane) : Nontrivial (Surface L₁ L₂ w) := by
  obtain ⟨p⟩ := OffSlitCharts.offOpen_nonempty L₁ w
  obtain ⟨q⟩ := OffSlitCharts.offOpen_nonempty L₂ w
  refine ⟨⟨leftOff L₁ L₂ w p, rightOff L₁ L₂ w q, ?_⟩⟩
  intro heq
  exact disjoint_left.mp (off_images_disjoint L₁ L₂ w) ⟨p, rfl⟩ ⟨q, heq.symm⟩

theorem regularSet_dense (L₁ L₂ : Lattice) (w : Plane)
    [T2Space (Surface L₁ L₂ w)] [ConnectedSpace (Surface L₁ L₂ w)] : Dense (regularSet L₁ L₂ w) := by
  let : Nontrivial (Surface L₁ L₂ w) := surfaceNontrivial L₁ L₂ w
  have hfinite : (endpointSet L₁ L₂ w).Finite := (finite_singleton _).insert _
  have h := (dense_univ : Dense (univ : Set (Surface L₁ L₂ w))).sdiff_finite hfinite
  have heq : (univ : Set (Surface L₁ L₂ w)) \ endpointSet L₁ L₂ w = regularSet L₁ L₂ w := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨mem_univ _, hx⟩⟩
  rwa [heq] at h

theorem regular_inclusion_denseRange (L₁ L₂ : Lattice) (w : Plane)
    [T2Space (Surface L₁ L₂ w)] [ConnectedSpace (Surface L₁ L₂ w)] :
    DenseRange (Subtype.val : Regular L₁ L₂ w → Surface L₁ L₂ w) :=
  denseRange_subtype_val.mpr (regularSet_dense L₁ L₂ w)

end MNEC.ChartAreaSupport

