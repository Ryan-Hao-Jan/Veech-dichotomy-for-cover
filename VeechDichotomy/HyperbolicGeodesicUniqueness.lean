module

public import VeechDichotomy.HyperbolicCanonicalSegments

/-! Actual metric geodesics in the Poincare plane are unique at fixed
constant-speed clocks. A metric-between point is determined by its
distance from the initial endpoint, by actual vertical clock coordinates.
The literal endpoint and pairwise distance equations then identify any
two genuine constant-speed geodesic paths. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicGeodesicUniqueness

open LinearGroup HyperbolicMetricSegments HyperbolicCanonicalSegments
open HyperbolicGeodesicLines HyperbolicCommonGeodesic Set
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

theorem real_clock_injective (s t u v : ℝ) (hu : u ∈ uIcc s t) (hv : v ∈ uIcc s t)
    (hd : dist s u = dist s v) : u = v := by
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hu hv
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.1),
      abs_of_nonpos (sub_nonpos.mpr hv.1)] at hd
    linarith only [hd]
  · rw [uIcc_of_ge h] at hu hv
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.2),
      abs_of_nonneg (sub_nonneg.mpr hv.2)] at hd
    linarith only [hd]

theorem segment_left_distance_injective (a b z w : ℍ) (hz : z ∈ metricSegment a b)
    (hw : w ∈ metricSegment a b) (hd : dist a z = dist a w) : z = w := by
  obtain ⟨A, c, s, t, hs, ht⟩ := exists_clock_coordinates a b
  change HyperbolicDirichletGeodesics.line A c s = a at hs
  change HyperbolicDirichletGeodesics.line A c t = b at ht
  have hz' : z ∈ metricSegment (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) := by rwa [hs, ht]
  have hw' : w ∈ metricSegment (HyperbolicDirichletGeodesics.line A c s) (HyperbolicDirichletGeodesics.line A c t) := by rwa [hs, ht]
  obtain ⟨hReZ, hClockZ⟩ := (normalized_between_iff A c s t z).mp hz'
  obtain ⟨hReW, hClockW⟩ := (normalized_between_iff A c s t w).mp hw'
  let τz := Real.log (A • z).im
  let τw := Real.log (A • w).im
  have hZ : verticalPoint c τz = A • z := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hReZ.symm
    · exact Real.exp_log (A • z).im_pos
  have hW : verticalPoint c τw = A • w := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hReW.symm
    · exact Real.exp_log (A • w).im_pos
  have hParamZ : HyperbolicDirichletGeodesics.line A c τz = z := by
    change A⁻¹ • verticalPoint c τz = z
    rw [hZ, inv_smul_smul]
  have hParamW : HyperbolicDirichletGeodesics.line A c τw = w := by
    change A⁻¹ • verticalPoint c τw = w
    rw [hW, inv_smul_smul]
  have hd' : dist s τz = dist s τw := by
    have h := hd
    rw [← hs, ← hParamZ, ← hParamW, HyperbolicDirichletGeodesics.line_distance,
      HyperbolicDirichletGeodesics.line_distance] at h
    exact h
  have hclock : τz = τw := real_clock_injective s t τz τw hClockZ hClockW hd'
  have heq : A • z = A • w := hZ.symm.trans ((congrArg (verticalPoint c) hclock).trans hW)
  have hi := congrArg (fun v : ℍ => A⁻¹ • v) heq
  simpa only [inv_smul_smul] using hi

theorem path_left_distance {a b : ℍ} (γ : Path a b)
    (hγ : ∀ s t : I, dist (γ s) (γ t) = dist a b * dist s.val t.val) (t : I) :
    dist a (γ t) = dist a b * t.val := by
  have h := hγ 0 t
  rw [γ.source] at h
  change dist a (γ t) = dist a b * dist (0 : ℝ) t.val at h
  simpa only [Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg t.property.1] using h

theorem path_right_distance {a b : ℍ} (γ : Path a b)
    (hγ : ∀ s t : I, dist (γ s) (γ t) = dist a b * dist s.val t.val) (t : I) :
    dist (γ t) b = dist a b * (1 - t.val) := by
  have h := hγ t 1
  rw [γ.target] at h
  change dist (γ t) b = dist a b * dist t.val (1 : ℝ) at h
  simpa only [Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] using h

theorem path_point_between {a b : ℍ} (γ : Path a b)
    (hγ : ∀ s t : I, dist (γ s) (γ t) = dist a b * dist s.val t.val) (t : I) :
    γ t ∈ metricSegment a b := by
  change dist a (γ t) + dist (γ t) b = dist a b
  rw [path_left_distance γ hγ, path_right_distance γ hγ]
  ring

theorem constantSpeed_path_unique {a b : ℍ} (γ δ : Path a b)
    (hγ : ∀ s t : I, dist (γ s) (γ t) = dist a b * dist s.val t.val)
    (hδ : ∀ s t : I, dist (δ s) (δ t) = dist a b * dist s.val t.val) : γ = δ := by
  apply Path.ext
  funext t
  apply segment_left_distance_injective a b (γ t) (δ t) (path_point_between γ hγ t) (path_point_between δ hδ t)
  rw [path_left_distance γ hγ, path_left_distance δ hδ]

end VeechDichotomy.HyperbolicGeodesicUniqueness
