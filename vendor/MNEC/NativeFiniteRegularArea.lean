module

public import MNEC.NativeOriginalChartArea
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Finite positive total physical regular area for an arbitrary genuine
native holomorphic differential. The original coefficient is analytically
continuous even at its zeros; a small native coordinate disk therefore has
a bounded actual Jacobian. Exact derived original-chart area comparison and
a finite compact original-curve cover give finiteness, without any supplied
density/integrability/area-bound or zero-cone certificate. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeFiniteRegularArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativePrimitiveJacobian
open NativeOriginalChartArea MeasureTheory Set Metric Topology Filter
open scoped Manifold ContDiff Classical ENNReal BigOperators
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem exists_original_disk_bound (q : Differential X) (b : X) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, 0 ≤ K ∧
      ball ((chartAt ℂ b) b) r ⊆ (chartAt ℂ b).target ∧
      ∀ z ∈ ball ((chartAt ℂ b) b) r, Complex.normSq (Jacobians.NativeCanonical.coeffAt q.val b z) ≤ K := by
  let c := Jacobians.NativeCanonical.coeffAt q.val b
  let a := (chartAt ℂ b) b
  let K := Complex.normSq (c a) + 1
  have ha : a ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hc : ContinuousAt (fun z => Complex.normSq (c z)) a :=
    Complex.continuous_normSq.continuousAt.comp (Jacobians.NativeCanonical.coeffAt_analyticAt q.val b ha).continuousAt
  have hK : Complex.normSq (c a) < K := by dsimp [K]; linarith
  have hn : (chartAt ℂ b).target ∩ {z | Complex.normSq (c z) < K} ∈ 𝓝 a :=
    inter_mem ((chartAt ℂ b).open_target.mem_nhds ha) (hc (isOpen_Iio.mem_nhds hK))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, K, ?_, fun z hz => (hball hz).1, fun z hz => (hball hz).2.le⟩
  dsimp [K]
  linarith [Complex.normSq_nonneg (c a)]

def chartNeighborhood (b : X) (r : ℝ) : Set X :=
  (chartAt ℂ b).source ∩ (chartAt ℂ b) ⁻¹' ball ((chartAt ℂ b) b) r

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartNeighborhood_open (b : X) (r : ℝ) : IsOpen (chartNeighborhood b r) :=
  (chartAt ℂ b).continuousOn.isOpen_inter_preimage (chartAt ℂ b).open_source isOpen_ball

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartNeighborhood_center (b : X) (r : ℝ) (hr : 0 < r) : b ∈ chartNeighborhood b r :=
  ⟨mem_chart_source ℂ b, mem_ball_self hr⟩

def disk (q : Differential X) (b : X) (r : ℝ) : Set Plane :=
  (originalCoordinate q b).target ∩ toPlane.symm ⁻¹' ball ((chartAt ℂ b) b) r

theorem disk_open (q : Differential X) (b : X) (r : ℝ) : IsOpen (disk q b r) :=
  (originalCoordinate q b).open_target.inter (isOpen_ball.preimage toPlane.symm.continuous)

theorem disk_volume_lt_top (q : Differential X) (b : X) (r : ℝ) : (volume : Measure Plane) (disk q b r) < (∞ : ℝ≥0∞) := by
  have hsub : disk q b r ⊆ toPlane '' closedBall ((chartAt ℂ b) b) r := by
    intro p hp
    exact ⟨toPlane.symm p, ball_subset_closedBall hp.2, ContinuousLinearEquiv.apply_symm_apply toPlane p⟩
  have hcompact : IsCompact (toPlane '' closedBall ((chartAt ℂ b) b) r) :=
    (isCompact_closedBall _ _).image toPlane.continuous
  exact (measure_mono hsub).trans_lt hcompact.measure_lt_top

theorem disk_image (q : Differential X) (b : X) (r : ℝ) :
    (originalCoordinate q b).symm '' disk q b r =
      (Subtype.val : Regular q → X) ⁻¹' chartNeighborhood b r := by
  let e := originalCoordinate q b
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (e.symm p).val ∈ (chartAt ℂ b).source := by
      have h := e.map_target hp.1
      rwa [originalCoordinate_source] at h
    have hcoord : (chartAt ℂ b) (e.symm p).val = toPlane.symm p := by
      have h := congrArg toPlane.symm (e.right_inv hp.1)
      simpa only [e, originalCoordinate_apply, ContinuousLinearEquiv.symm_apply_apply] using h
    refine ⟨hx, ?_⟩
    change (chartAt ℂ b) (e.symm p).val ∈ ball ((chartAt ℂ b) b) r
    rw [hcoord]
    exact hp.2
  · intro hx
    have hxs : x ∈ e.source := by rw [originalCoordinate_source]; exact hx.1
    refine ⟨e x, ⟨e.map_source hxs, ?_⟩, e.left_inv hxs⟩
    change toPlane.symm (e x) ∈ ball ((chartAt ℂ b) b) r
    rw [originalCoordinate_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact hx.2

/-- Every ORIGINAL point, including a zero of q, has a native neighborhood
whose actual regular physical area is finite. -/
theorem exists_finite_original_neighborhood (q : Differential X) (b : X) :
    ∃ U : Set X, IsOpen U ∧ b ∈ U ∧
      NativeRegularArea.regularArea q ((Subtype.val : Regular q → X) ⁻¹' U) < (∞ : ℝ≥0∞) := by
  obtain ⟨r, hr, K, _, _, hbound⟩ := exists_original_disk_bound q b
  refine ⟨chartNeighborhood b r, chartNeighborhood_open b r, chartNeighborhood_center b r hr, ?_⟩
  rw [← disk_image q b r]
  have hweight : ∀ p ∈ disk q b r, density q b p ≤ ENNReal.ofReal K := by
    intro p hp
    exact ENNReal.ofReal_le_ofReal (hbound (toPlane.symm p) hp.2)
  have hmass := original_image_area_le q b (disk q b r) (disk_open q b r).measurableSet
    inter_subset_left (ENNReal.ofReal K) hweight
  exact hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (disk_volume_lt_top q b r))

theorem regularArea_isFinite (q : Differential X) : IsFiniteMeasure (NativeRegularArea.regularArea q) where
  measure_univ_lt_top := by
    choose U hU hcenter hfinite using exists_finite_original_neighborhood q
    obtain ⟨F, hcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover U hU
      (fun x _ => mem_iUnion.mpr ⟨x, hcenter x⟩)
    have hsub : (univ : Set (Regular q)) ⊆ ⋃ b ∈ F, (Subtype.val : Regular q → X) ⁻¹' U b := by
      intro x _
      obtain ⟨b, hb⟩ := mem_iUnion.mp (hcover (mem_univ x.val))
      obtain ⟨hbF, hx⟩ := mem_iUnion.mp hb
      exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hbF, hx⟩⟩
    have hbound : NativeRegularArea.regularArea q (⋃ b ∈ F, (Subtype.val : Regular q → X) ⁻¹' U b) ≤
        ∑ b ∈ F, NativeRegularArea.regularArea q ((Subtype.val : Regular q → X) ⁻¹' U b) :=
      measure_biUnion_finset_le F _
    exact (measure_mono hsub).trans_lt (hbound.trans_lt (ENNReal.sum_lt_top.mpr (fun b _ => hfinite b)))

theorem regularArea_univ_pos (q : Differential X) : 0 < NativeRegularArea.regularArea q univ :=
  NativeRegularArea.positive_open_mass q univ isOpen_univ ⟨Classical.choice (regular_nonempty q), mem_univ _⟩

theorem regularArea_univ_ne_top (q : Differential X) : NativeRegularArea.regularArea q univ ≠ (∞ : ℝ≥0∞) :=
  (regularArea_isFinite q).measure_univ_lt_top.ne

def totalArea (q : Differential X) : ℝ := (NativeRegularArea.regularArea q univ).toReal

theorem totalArea_pos (q : Differential X) : 0 < totalArea q :=
  ENNReal.toReal_pos (regularArea_univ_pos q).ne' (regularArea_univ_ne_top q)

theorem ofReal_totalArea (q : Differential X) : ENNReal.ofReal (totalArea q) = NativeRegularArea.regularArea q univ :=
  ENNReal.ofReal_toReal (regularArea_univ_ne_top q)

end MNEC.NativeFiniteRegularArea
