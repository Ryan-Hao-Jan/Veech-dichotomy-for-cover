module

public import MNEC.NativePrimitiveJacobian
public import MNEC.NativeRegularArea

/-! The constructed canonical regular area has its actual original-chart
coefficient density. Change of variables proves the formula on each
primitive overlap; countable disjoint regular patches prove it on an entire
original-coordinate regular domain. No density/integrability/area oracle is
assumed, and zeros need no artificial continuation of a primitive inverse. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeOriginalChartArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativePrimitiveAreaCharts NativePrimitiveJacobian MeasureTheory Set Topology Filter
open scoped Manifold ContDiff Classical ENNReal
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def density (q : Differential X) (b : X) (p : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (Complex.normSq (Jacobians.NativeCanonical.coeffAt q.val b (toPlane.symm p)))

theorem primitive_overlap_area (q : Differential X) (b : X) (i : Index q) (B : Set Plane)
    (hB : MeasurableSet B) (hsub : B ⊆ (transition q b i).source) :
    NativeRegularArea.regularArea q ((originalCoordinate q b).symm '' B) =
      ∫⁻ p in B, density q b p := by
  have hBo : B ⊆ (originalCoordinate q b).target := fun p hp => (hsub hp).1
  have hA : MeasurableSet ((originalCoordinate q b).symm '' B) :=
    LocalPhysicalAreaTransport.measurableSet_image_of_subset_source (originalCoordinate q b).symm B hB hBo
  have hAsub : (originalCoordinate q b).symm '' B ⊆ (chart q i).source := by
    rintro y ⟨p, hp, rfl⟩
    exact (hsub hp).2
  have himage : chart q i '' ((originalCoordinate q b).symm '' B) = transition q b i '' B := by
    rw [image_image]
    rfl
  have hJac := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure Plane)
    (f := transition q b i)
    (f' := fun p => realMul (Jacobians.NativeCanonical.coeffAt q.val b (toPlane.symm p)))
    hB (fun p hp => (transition_derivative q b i p (hsub hp)).hasFDerivWithinAt)
    ((transition q b i).injOn.mono hsub)
  rw [NativeRegularArea.primitive_chart_formula q i _ hA hAsub, himage]
  simpa only [density, realMul_abs_det] using hJac.symm

/-- Exact coefficient-density formula on the actual regular part of ANY
original native chart, derived by genuine countable overlap gluing. -/
theorem original_image_area (q : Differential X) (b : X) (B : Set Plane)
    (hB : MeasurableSet B) (hsub : B ⊆ (originalCoordinate q b).target) :
    NativeRegularArea.regularArea q ((originalCoordinate q b).symm '' B) =
      ∫⁻ p in B, density q b p := by
  let U : Index q → Set Plane := fun i => (transition q b i).source
  have hU : ∀ i, IsOpen (U i) := fun i => (transition q b i).open_source
  have hcover : (originalCoordinate q b).target ⊆ ⋃ i, U i := by
    intro p hp
    obtain ⟨i, hi⟩ := covers q ((originalCoordinate q b).symm p)
    exact mem_iUnion.mpr ⟨i, hp, hi⟩
  let : Nonempty (Index q) := index_nonempty q
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof (originalCoordinate q b).target).indexed_countable_subcover U hU hcover
  let D : ℕ → Set Plane := fun n => B ∩ U (f n)
  let C : ℕ → Set Plane := disjointed D
  have hC : ∀ n, MeasurableSet (C n) := MeasurableSet.disjointed (fun n => hB.inter (hU (f n)).measurableSet)
  have hCB (n : ℕ) : C n ⊆ B := (disjointed_subset D n).trans inter_subset_left
  have hCU (n : ℕ) : C n ⊆ U (f n) := (disjointed_subset D n).trans inter_subset_right
  have hCo (n : ℕ) : C n ⊆ (originalCoordinate q b).target := (hCB n).trans hsub
  have hUnion : ⋃ n : ℕ, C n = B := by
    rw [iUnion_disjointed]
    change (⋃ n : ℕ, B ∩ U (f n)) = B
    rw [← inter_iUnion, inter_eq_left.mpr (hsub.trans hf)]
  have hDisj : Pairwise (fun n k : ℕ => Disjoint (C n) (C k)) := disjoint_disjointed D
  have hImMeas : ∀ n, MeasurableSet ((originalCoordinate q b).symm '' C n) := fun n =>
    LocalPhysicalAreaTransport.measurableSet_image_of_subset_source (originalCoordinate q b).symm (C n) (hC n) (hCo n)
  have hImDisj : Pairwise (fun n k : ℕ => Disjoint ((originalCoordinate q b).symm '' C n)
      ((originalCoordinate q b).symm '' C k)) := by
    intro n k hnk
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨z, hz, hzy⟩
    have hpz := (originalCoordinate q b).symm.injOn (hCo n hp) (hCo k hz) (hpy.trans hzy.symm)
    subst z
    exact disjoint_left.mp (hDisj hnk) hp hz
  calc
    NativeRegularArea.regularArea q ((originalCoordinate q b).symm '' B) =
        ∑' n : ℕ, NativeRegularArea.regularArea q ((originalCoordinate q b).symm '' C n) := by
      rw [← hUnion, image_iUnion, measure_iUnion hImDisj hImMeas]
    _ = ∑' n : ℕ, ∫⁻ p in C n, density q b p := tsum_congr (fun n => primitive_overlap_area q b (f n) (C n) (hC n) (hCU n))
    _ = ∫⁻ p in B, density q b p := by rw [← hUnion, lintegral_iUnion hC hDisj]

theorem original_image_area_le (q : Differential X) (b : X) (B : Set Plane)
    (hB : MeasurableSet B) (hsub : B ⊆ (originalCoordinate q b).target)
    (K : ℝ≥0∞) (hbound : ∀ p ∈ B, density q b p ≤ K) :
    NativeRegularArea.regularArea q ((originalCoordinate q b).symm '' B) ≤ K * volume B := by
  rw [original_image_area q b B hB hsub]
  calc
    (∫⁻ p in B, density q b p) ≤ ∫⁻ _p in B, K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with p hp
      exact hbound p hp
    _ = K * volume B := by simp only [lintegral_const, Measure.restrict_apply_univ]

end MNEC.NativeOriginalChartArea
