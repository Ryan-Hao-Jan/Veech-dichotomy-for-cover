module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# Unique maximal native integral curves through an initial point

The domain is the union of all bounded open-interval native integral curves
through `x₀` at time zero. Mathlib's C¹ uniqueness proves that these curves
agree wherever they overlap. A choice from this coherent family defines a
native integral curve on the open interval union. Mathlib's local existence
proves that the union contains zero. Every other solution on an open real
interval is proved to be a restriction of this one.

Values of a curve outside its interval are junk, as in mathlib's native
integral-curve API. Uniqueness is consequently asserted on the actual
maximal domain, rather than for irrelevant values outside that domain.
No maximality oracle, continuation field, or actual-flow assumption occurs.
-/

noncomputable section

namespace MNEC.MaximalIntegralCurve

open Set Filter Function
open scoped Manifold Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

structure Segment (v : (x : M) → TangentSpace I x) (x₀ : M) where
  a : ℝ
  b : ℝ
  a_neg : a < 0
  b_pos : 0 < b
  curve : ℝ → M
  initial : curve 0 = x₀
  integral : IsMIntegralCurveOn curve v (Ioo a b)

def Segment.interval {v : (x : M) → TangentSpace I x} {x₀ : M} (c : Segment v x₀) : Set ℝ :=
  Ioo c.a c.b

theorem Segment.zero_mem {v : (x : M) → TangentSpace I x} {x₀ : M} (c : Segment v x₀) :
    0 ∈ c.interval := ⟨c.a_neg, c.b_pos⟩

def maximalDomain (v : (x : M) → TangentSpace I x) (x₀ : M) : Set ℝ :=
  ⋃ c : Segment v x₀, c.interval

theorem segment_subset_maximalDomain {v : (x : M) → TangentSpace I x} {x₀ : M}
    (c : Segment v x₀) : c.interval ⊆ maximalDomain v x₀ :=
  subset_iUnion (fun c : Segment v x₀ => c.interval) c

theorem maximalDomain_open (v : (x : M) → TangentSpace I x) (x₀ : M) :
    IsOpen (maximalDomain v x₀) := isOpen_iUnion fun _ => isOpen_Ioo

theorem maximalDomain_ordConnected (v : (x : M) → TangentSpace I x) (x₀ : M) :
    OrdConnected (maximalDomain v x₀) := by
  constructor
  intro s hs t ht u hu
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hs
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp ht
  by_cases hu0 : u ≤ 0
  · exact Set.mem_iUnion.mpr ⟨c, hc.1.trans_le hu.1, hu0.trans_lt c.b_pos⟩
  · exact Set.mem_iUnion.mpr
      ⟨d, d.a_neg.trans_le (le_of_lt (lt_of_not_ge hu0)), hu.2.trans_lt hd.2⟩

theorem maximalDomain_convex (v : (x : M) → TangentSpace I x) (x₀ : M) :
    Convex ℝ (maximalDomain v x₀) := (maximalDomain_ordConnected v x₀).convex

def segmentAt (v : (x : M) → TangentSpace I x) (x₀ : M) (t : ℝ)
    (ht : t ∈ maximalDomain v x₀) : Segment v x₀ := (Set.mem_iUnion.mp ht).choose

theorem mem_segmentAt (v : (x : M) → TangentSpace I x) (x₀ : M) (t : ℝ)
    (ht : t ∈ maximalDomain v x₀) : t ∈ (segmentAt v x₀ t ht).interval :=
  (Set.mem_iUnion.mp ht).choose_spec

def maximalCurve (v : (x : M) → TangentSpace I x) (x₀ : M) (t : ℝ) : M :=
  if ht : t ∈ maximalDomain v x₀ then (segmentAt v x₀ t ht).curve t else x₀

section Uniqueness

variable [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {x₀ : M}

theorem segments_agree
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (c d : Segment v x₀) :
    EqOn c.curve d.curve (Ioo (max c.a d.a) (min c.b d.b)) := by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) (I := I) (v := v) _ hv
    (c.integral.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
    (d.integral.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
    (c.initial.trans d.initial.symm)
  exact ⟨max_lt c.a_neg d.a_neg, lt_min c.b_pos d.b_pos⟩

theorem maximalCurve_eq_segment
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (c : Segment v x₀) : EqOn (maximalCurve v x₀) c.curve c.interval := by
  intro t ht
  have htD := segment_subset_maximalDomain c ht
  rw [maximalCurve, dite_eq_left htD]
  have hchosen := mem_segmentAt v x₀ t htD
  exact segments_agree hv (segmentAt v x₀ t htD) c
    ⟨max_lt hchosen.1 ht.1, lt_min hchosen.2 ht.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem maximalCurve_isMIntegralCurveOn
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    IsMIntegralCurveOn (maximalCurve v x₀) v (maximalDomain v x₀) := by
  intro t ht
  obtain ⟨c, htc⟩ := Set.mem_iUnion.mp ht
  have hEq : maximalCurve v x₀ =ᶠ[𝓝 t] c.curve := by
    filter_upwards [Ioo_mem_nhds htc.1 htc.2] with s hs
    exact maximalCurve_eq_segment hv c hs
  have hd := (c.integral t htc).hasMFDerivAt (Ioo_mem_nhds htc.1 htc.2)
  have hdm := hd.congr_of_eventuallyEq_abuse hEq
  have hvalue : maximalCurve v x₀ t = c.curve t := hEq.self_of_nhds
  have hderivative : ((1 : ℝ →L[ℝ] ℝ).smulRight (v (c.curve t))) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (maximalCurve v x₀ t))) := by
    rw [hvalue]
  exact (hdm.congr_mfderiv hderivative).hasMFDerivWithinAt

/-- Every point of an open real interval containing zero is enclosed with
zero in a bounded open subinterval contained in the original interval. -/
theorem exists_bounded_interval_inside {U : Set ℝ} (hU : IsOpen U) (hord : OrdConnected U)
    (hzero : 0 ∈ U) {t : ℝ} (ht : t ∈ U) :
    ∃ a b : ℝ, 0 ∈ Ioo a b ∧ t ∈ Ioo a b ∧ Ioo a b ⊆ U := by
  have hlo : min (0 : ℝ) t ∈ U := by
    by_cases h : 0 ≤ t
    · simpa only [min_eq_left h] using hzero
    · simpa only [min_eq_right (le_of_not_ge h)] using ht
  have hhi : max (0 : ℝ) t ∈ U := by
    by_cases h : 0 ≤ t
    · simpa only [max_eq_right h] using ht
    · simpa only [max_eq_left (le_of_not_ge h)] using hzero
  obtain ⟨a, c, ⟨hal, hlc⟩, hac⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hlo)
  obtain ⟨d, b, ⟨hdh, hhb⟩, hdb⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hhi)
  let A := (a + min 0 t) / 2
  let B := (max 0 t + b) / 2
  have hA : A ∈ U := hac ⟨by dsimp [A]; linarith, by dsimp [A]; linarith⟩
  have hB : B ∈ U := hdb ⟨by dsimp [B]; linarith, by dsimp [B]; linarith⟩
  have hA0 : A < 0 := by dsimp [A]; linarith [min_le_left (0 : ℝ) t]
  have hAt : A < t := by dsimp [A]; linarith [min_le_right (0 : ℝ) t]
  have hB0 : 0 < B := by dsimp [B]; linarith [le_max_left (0 : ℝ) t]
  have hBt : t < B := by dsimp [B]; linarith [le_max_right (0 : ℝ) t]
  exact ⟨A, B, ⟨hA0, hB0⟩, ⟨hAt, hBt⟩,
    fun s hs => hord.out hA hB (Ioo_subset_Icc_self hs)⟩

/-- Every native solution on any open real interval through the same
initial point is a restriction of the constructed union solution. -/
theorem extends_every_open_interval
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (U : Set ℝ) (δ : ℝ → M) (hU : IsOpen U) (hord : OrdConnected U) (hzero : 0 ∈ U)
    (hδzero : δ 0 = x₀) (hδ : IsMIntegralCurveOn δ v U) :
    U ⊆ maximalDomain v x₀ ∧ EqOn (maximalCurve v x₀) δ U := by
  have hsegment (t : ℝ) (ht : t ∈ U) :
      ∃ c : Segment v x₀, t ∈ c.interval ∧ c.curve = δ := by
    obtain ⟨a, b, h0, ht', hsub⟩ := exists_bounded_interval_inside hU hord hzero ht
    exact ⟨⟨a, b, h0.1, h0.2, δ, hδzero, hδ.mono hsub⟩, ht', rfl⟩
  constructor
  · intro t ht
    obtain ⟨c, htc, _⟩ := hsegment t ht
    exact segment_subset_maximalDomain c htc
  · intro t ht
    obtain ⟨c, htc, hcurve⟩ := hsegment t ht
    rw [← hcurve]
    exact maximalCurve_eq_segment hv c htc

theorem no_proper_open_interval_extension
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (U : Set ℝ) (δ : ℝ → M) (hU : IsOpen U) (hord : OrdConnected U) (hzero : 0 ∈ U)
    (hδzero : δ 0 = x₀) (hδ : IsMIntegralCurveOn δ v U)
    (hcontains : maximalDomain v x₀ ⊆ U) :
    U = maximalDomain v x₀ ∧ EqOn (maximalCurve v x₀) δ U := by
  obtain ⟨hsub, heq⟩ := extends_every_open_interval hv U δ hU hord hzero hδzero hδ
  exact ⟨Set.Subset.antisymm hsub hcontains, heq⟩

end Uniqueness

section Existence

variable [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {x₀ : M}

omit [T2Space M] in
theorem exists_segment
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) : Nonempty (Segment v x₀) := by
  obtain ⟨γ, hγzero, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := I) (v := v) (x₀ := x₀) (0 : ℝ) hv.contMDiffAt
  obtain ⟨ε, hε, hεcurve⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hcurve : IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεcurve
  exact ⟨⟨-ε, ε, neg_lt_zero.mpr hε, hε, γ, hγzero, hcurve⟩⟩

omit [T2Space M] in
theorem zero_mem_maximalDomain
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    0 ∈ maximalDomain v x₀ := by
  obtain ⟨c⟩ := exists_segment (x₀ := x₀) hv
  exact segment_subset_maximalDomain c c.zero_mem

theorem maximalCurve_initial
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) : maximalCurve v x₀ 0 = x₀ := by
  obtain ⟨c⟩ := exists_segment (x₀ := x₀) hv
  exact (maximalCurve_eq_segment hv c c.zero_mem).trans c.initial

omit [T2Space M] in
theorem maximalDomain_connected
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    IsConnected (maximalDomain v x₀) :=
  ⟨⟨0, zero_mem_maximalDomain hv⟩, (maximalDomain_convex v x₀).isPreconnected⟩

theorem unique_on_maximalDomain
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (δ : ℝ → M) (hδzero : δ 0 = x₀) (hδ : IsMIntegralCurveOn δ v (maximalDomain v x₀)) :
    EqOn (maximalCurve v x₀) δ (maximalDomain v x₀) :=
  (extends_every_open_interval hv _ δ (maximalDomain_open v x₀)
    (maximalDomain_ordConnected v x₀) (zero_mem_maximalDomain hv) hδzero hδ).2

/-- A proved maximal native integral curve, with its genuine open interval
domain and the full restriction property against every other interval solution. -/
theorem exists_maximal_integralCurve
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ (D : Set ℝ) (γ : ℝ → M), IsOpen D ∧ Convex ℝ D ∧ IsConnected D ∧ 0 ∈ D ∧
      γ 0 = x₀ ∧ IsMIntegralCurveOn γ v D ∧
      ∀ (U : Set ℝ) (δ : ℝ → M), IsOpen U → OrdConnected U → 0 ∈ U → δ 0 = x₀ →
        IsMIntegralCurveOn δ v U → U ⊆ D ∧ EqOn γ δ U := by
  exact ⟨maximalDomain v x₀, maximalCurve v x₀, maximalDomain_open v x₀,
    maximalDomain_convex v x₀, maximalDomain_connected hv, zero_mem_maximalDomain hv,
    maximalCurve_initial hv, maximalCurve_isMIntegralCurveOn hv,
    extends_every_open_interval hv⟩

end Existence

end MNEC.MaximalIntegralCurve
