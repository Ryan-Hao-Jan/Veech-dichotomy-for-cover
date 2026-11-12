module

public import VeechDichotomy.HyperbolicDirichletGeodesics
public import Mathlib.Analysis.Convex.StrictConvexBetween

/-! Genuine metric betweenness in the Poincare upper half-plane.
Equality in the log-height distance bound forces equal real parts;
equality in a vertical triangle inequality then forces the actual point
onto the vertical interval of logarithmic heights. All statements use
the actual metric and actual SL2 isometries. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicMetricSegments

open LinearGroup HyperbolicGeodesicLines Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem log_distance_eq_iff (z w : ℍ) :
    dist (Real.log z.im) (Real.log w.im) = dist z w ↔ z.re = w.re := by
  constructor
  · intro h
    let v : ℍ := ⟨⟨z.re, w.im⟩, w.im_pos⟩
    have hv : dist z v = dist (Real.log z.im) (Real.log w.im) :=
      UpperHalfPlane.dist_of_re_eq rfl
    have heq : dist z w = dist z v := h.symm.trans hv.symm
    have hc := congrArg Real.cosh heq
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
    change ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) =
      ((z.re - z.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) at hc
    have hd : 2 * z.im * w.im ≠ 0 := by positivity
    have hm := congrArg (fun r : ℝ => r * (2 * z.im * w.im)) hc
    simp only [div_mul_cancel₀ _ hd] at hm
    have hs : (z.re - w.re) ^ 2 = 0 := by nlinarith only [hm]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)
  · intro h
    exact (UpperHalfPlane.dist_of_re_eq h).symm

theorem real_between_iff (s t u : ℝ) :
    dist s u + dist u t = dist s t ↔ u ∈ uIcc s t := by
  rw [dist_add_dist_eq_iff, ← mem_segment_iff_wbtw, segment_eq_uIcc]

theorem vertical_between_iff (c s t : ℝ) (z : ℍ) :
    dist (verticalPoint c s) z + dist z (verticalPoint c t) = dist (verticalPoint c s) (verticalPoint c t) ↔
      z.re = c ∧ Real.log z.im ∈ uIcc s t := by
  constructor
  · intro h
    have h₀ := UpperHalfPlane.dist_log_im_le (verticalPoint c s) z
    have h₁ := UpperHalfPlane.dist_log_im_le z (verticalPoint c t)
    change dist (Real.log (Real.exp s)) (Real.log z.im) ≤ dist (verticalPoint c s) z at h₀
    change dist (Real.log z.im) (Real.log (Real.exp t)) ≤ dist z (verticalPoint c t) at h₁
    rw [Real.log_exp] at h₀ h₁
    have htri := dist_triangle s (Real.log z.im) t
    have hv := (vertical_isometry c).dist_eq s t
    have heq₀ : dist s (Real.log z.im) = dist (verticalPoint c s) z := by linarith only [h, h₀, h₁, htri, hv]
    have hsum : dist s (Real.log z.im) + dist (Real.log z.im) t = dist s t := by linarith only [h, h₀, h₁, htri, hv]
    have hnative : dist (Real.log (verticalPoint c s).im) (Real.log z.im) = dist (verticalPoint c s) z := by
      change dist (Real.log (Real.exp s)) (Real.log z.im) = _
      rwa [Real.log_exp]
    have hre := (log_distance_eq_iff (verticalPoint c s) z).mp hnative
    exact ⟨hre.symm, (real_between_iff s t (Real.log z.im)).mp hsum⟩
  · rintro ⟨hre, hclock⟩
    have h₀ := UpperHalfPlane.dist_of_re_eq (show (verticalPoint c s).re = z.re from hre.symm)
    have h₁ := UpperHalfPlane.dist_of_re_eq (show z.re = (verticalPoint c t).re from hre)
    change dist (verticalPoint c s) z = dist (Real.log (Real.exp s)) (Real.log z.im) at h₀
    change dist z (verticalPoint c t) = dist (Real.log z.im) (Real.log (Real.exp t)) at h₁
    rw [Real.log_exp] at h₀ h₁
    rw [h₀, h₁, (vertical_isometry c).dist_eq]
    exact (real_between_iff s t (Real.log z.im)).mpr hclock

def metricSegment (a b : ℍ) : Set ℍ := {z | dist a z + dist z b = dist a b}

theorem smul_mem_metricSegment_iff (A : SL2) (a b z : ℍ) :
    A • z ∈ metricSegment (A • a) (A • b) ↔ z ∈ metricSegment a b := by
  change dist (A • a) (A • z) + dist (A • z) (A • b) = dist (A • a) (A • b) ↔ _
  rw [dist_smul, dist_smul, dist_smul]
  rfl

theorem image_metricSegment (A : SL2) (a b : ℍ) :
    (fun z : ℍ => A • z) '' metricSegment a b = metricSegment (A • a) (A • b) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (smul_mem_metricSegment_iff A a b z).mpr hz
  · intro z hz
    refine ⟨A⁻¹ • z, ?_, smul_inv_smul A z⟩
    apply (smul_mem_metricSegment_iff A a b (A⁻¹ • z)).mp
    simpa only [smul_inv_smul] using hz

end VeechDichotomy.HyperbolicMetricSegments
