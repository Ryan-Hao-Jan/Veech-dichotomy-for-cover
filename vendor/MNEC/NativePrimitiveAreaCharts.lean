module

public import MNEC.NativeRegularTranslationAtlas

/-! ALL genuine q-primitive charts, not only a selected pointwise family.
Their source restrictions and standard real physical coordinates preserve
the proved intrinsic derivative identities and translation compatibility.
This family permits measure uniqueness independently of primitive choices. -/

@[expose] public section
noncomputable section
namespace MNEC.NativePrimitiveAreaCharts

open LatticeTorus NativeAbelianDifferential NativePrimitiveTransitions NativeRegularTranslationAtlas
open Set Filter Topology
open scoped Manifold ContDiff Classical
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev Index (q : Differential X) := Σ x : Regular q, PrimitiveChart q x

def complexChart (q : Differential X) (i : Index q) : OpenPartialHomeomorph (Regular q) ℂ :=
  i.2.chart.subtypeRestr (s := regularOpen q) (regular_nonempty q)

def chart (q : Differential X) (i : Index q) : OpenPartialHomeomorph (Regular q) Plane :=
  (complexChart q i).transHomeomorph toPlane.toHomeomorph

theorem chart_source (q : Differential X) (i : Index q) :
    (chart q i).source = Subtype.val ⁻¹' i.2.chart.source :=
  i.2.chart.subtypeRestr_source (s := regularOpen q) (regular_nonempty q)

theorem chart_apply (q : Differential X) (i : Index q) (x : Regular q) :
    chart q i x = toPlane (i.2.chart x.val) := rfl

theorem complexChart_target (q : Differential X) (i : Index q) :
    (complexChart q i).target = i.2.chart.target := by
  apply Subset.antisymm
  · exact i.2.chart.subtypeRestr_target_subset _
  · intro z hz
    let y : Regular q := ⟨i.2.chart.symm z, i.2.regular_source (i.2.chart.map_target hz)⟩
    have hy : y.val ∈ i.2.chart.source := i.2.chart.map_target hz
    have hmem := i.2.chart.map_subtype_source (s := regularOpen q) (regular_nonempty q) (x := y) hy
    have heq : i.2.chart y.val = z := i.2.chart.right_inv hz
    rwa [heq] at hmem

theorem chart_target (q : Differential X) (i : Index q) :
    (chart q i).target = toPlane.symm ⁻¹' i.2.chart.target := by
  change toPlane.symm ⁻¹' (complexChart q i).target = _
  rw [complexChart_target]

theorem chart_symm_value (q : Differential X) (i : Index q) (p : Plane)
    (hp : p ∈ (chart q i).target) : ((chart q i).symm p).val = i.2.chart.symm (toPlane.symm p) := by
  let y := (chart q i).symm p
  have hy : y.val ∈ i.2.chart.source := by
    have h := (chart q i).map_target hp
    rwa [chart_source] at h
  have heq : toPlane (i.2.chart y.val) = p := (chart q i).right_inv hp
  have hraw : i.2.chart y.val = toPlane.symm p := by
    apply toPlane.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact heq
  calc
    y.val = i.2.chart.symm (i.2.chart y.val) := (i.2.chart.left_inv hy).symm
    _ = _ := by rw [hraw]

def selectedIndex (q : Differential X) (x : Regular q) : Index q := ⟨x, chosen q x⟩

theorem chart_selected (q : Differential X) (x : Regular q) :
    chart q (selectedIndex q x) = coordinateChart q x := rfl

theorem covers (q : Differential X) (x : Regular q) : ∃ i : Index q, x ∈ (chart q i).source :=
  ⟨selectedIndex q x, coordinateChart_center q x⟩

theorem index_nonempty (q : Differential X) : Nonempty (Index q) :=
  ⟨selectedIndex q (Classical.choice (regular_nonempty q))⟩

theorem transition_locally_translation (q : Differential X) (i j : Index q) :
    TranslationGroupoid.LocallyTranslationOn ((chart q i).symm.trans (chart q j))
      ((chart q i).symm.trans (chart q j)).source := by
  intro p hp
  have hp₁ : toPlane.symm p ∈ i.2.chart.target := by
    have hpt : p ∈ (chart q i).target := hp.1
    rw [chart_target] at hpt
    exact hpt
  have hp₂ : i.2.chart.symm (toPlane.symm p) ∈ j.2.chart.source := by
    have h := hp.2
    rw [chart_source] at h
    change ((chart q i).symm p).val ∈ j.2.chart.source at h
    rwa [chart_symm_value q i p hp.1] at h
  obtain ⟨a, ha⟩ := NativePrimitiveTransitions.transition_germ q i.2.chart j.2.chart
    i.2.derivative j.2.derivative (toPlane.symm p) ⟨hp₁, hp₂⟩
  refine ⟨toPlane a, ?_⟩
  have hc : ContinuousAt toPlane.symm p := toPlane.symm.continuous.continuousAt
  filter_upwards [((chart q i).symm.trans (chart q j)).open_source.mem_nhds hp, hc ha] with z hz htrans
  change toPlane (j.2.chart ((chart q i).symm z).val) = z + toPlane a
  rw [chart_symm_value q i z hz.1]
  change toPlane ((i.2.chart.symm.trans j.2.chart) (toPlane.symm z)) = _
  rw [htrans, map_add, ContinuousLinearEquiv.apply_symm_apply]

end MNEC.NativePrimitiveAreaCharts
