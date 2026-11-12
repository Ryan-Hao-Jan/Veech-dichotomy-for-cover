module

public import VeechDichotomy.ComplexAffineLineSegments
public import VeechDichotomy.HyperbolicCanonicalSegments

/-! The Klein image of every actual Poincare metric segment is precisely
the ordinary Euclidean segment. Complete normalized geodesics are actual
bisectors of a reflected pair of points. Their Klein images lie in genuine
affine lines with nonzero normals; continuous injectivity then identifies
all interval images. No line, range or betweenness axiom is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinGeodesics

open LinearGroup Set HyperbolicKleinMap HyperbolicKleinHomeomorph
open HyperbolicKleinHalfPlanes HyperbolicBisectorNull HyperbolicGeodesicLines
open HyperbolicDirichletGeodesics HyperbolicMetricSegments HyperbolicCanonicalSegments
open HyperbolicCommonGeodesic
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

theorem normal_nonzero {p q : ℍ} (hpq : p ≠ q) :
    (linear p q / 2) ^ 2 + ((leading p q - constant p q) / 2) ^ 2 ≠ 0 := by
  intro hsum
  have hr : linear p q / 2 = 0 := by nlinarith [sq_nonneg ((leading p q - constant p q) / 2)]
  have hi : (leading p q - constant p q) / 2 = 0 := by nlinarith [sq_nonneg (linear p q / 2)]
  have hp : affineForm p q (point p) < 0 :=
    (HyperbolicKleinHalfPlanes.dist_lt_iff p q p).mp (by simpa using dist_pos.mpr hpq)
  have hq : ¬affineForm p q (point q) ≤ 0 := by
    intro hq
    have hd := (HyperbolicKleinHalfPlanes.dist_le_iff p q q).mpr hq
    rw [dist_self] at hd
    exact (dist_pos.mpr hpq.symm).not_ge hd
  simp only [affineForm, hr, hi, zero_mul, add_zero] at hp hq
  exact hq hp.le

theorem bisector_mem_affineLine (p q z : ℍ) (hz : dist z p = dist z q) :
    point z ∈ ComplexAffineLineSegments.affineLine (linear p q / 2)
      ((leading p q - constant p q) / 2) (-(leading p q + constant p q) / 2) := by
  have h := (HyperbolicKleinHalfPlanes.dist_eq_iff p q z).mp hz
  change ComplexAffineLineSegments.normal _ _ (point z) = _
  simp only [ComplexAffineLineSegments.normal, add_apply, smul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  unfold affineForm at h
  linarith

def reflectionLeft (c : ℝ) : ℍ := ⟨⟨c - 1, 1⟩, by norm_num⟩
def reflectionRight (c : ℝ) : ℍ := ⟨⟨c + 1, 1⟩, by norm_num⟩

theorem reflection_ne (c : ℝ) : reflectionLeft c ≠ reflectionRight c := by
  intro he
  have hr := congrArg UpperHalfPlane.re he
  change c - 1 = c + 1 at hr
  linarith

theorem reflection_bisector (c : ℝ) (z : ℍ) :
    dist z (reflectionLeft c) = dist z (reflectionRight c) ↔ z.re = c := by
  rw [HyperbolicDistanceComparison.dist_eq_iff]
  have hf : HyperbolicDistanceComparison.form (reflectionLeft c) (reflectionRight c) z =
      4 * (z.re - c) := by
    change (1 - 1) * Complex.normSq (z : ℂ) +
      (-2 * (1 * (c - 1) - 1 * (c + 1))) * z.re +
      (1 * ((c - 1) ^ 2 + 1 ^ 2) - 1 * ((c + 1) ^ 2 + 1 ^ 2)) = _
    ring
  rw [hf]
  constructor <;> intro h <;> linarith

theorem line_bisector (A : SL2) (c t : ℝ) :
    dist (line A c t) (A⁻¹ • reflectionLeft c) =
      dist (line A c t) (A⁻¹ • reflectionRight c) := by
  unfold line
  rw [dist_smul, dist_smul]
  exact (reflection_bisector c (verticalPoint c t)).mpr rfl

theorem image_line_interval (A : SL2) (c s t : ℝ) :
    (fun u => point (line A c u)) '' uIcc s t =
      segment ℝ (point (line A c s)) (point (line A c t)) := by
  let p := A⁻¹ • reflectionLeft c
  let q := A⁻¹ • reflectionRight c
  have hpq : p ≠ q := fun he => reflection_ne c ((MulAction.injective A⁻¹) he)
  have hpoint : Function.Injective point := fun z w he =>
    homeomorph.injective (Subtype.ext he)
  exact ComplexAffineLineSegments.image_interval _
    (continuous_point.comp (line_isometry A c).continuous)
    (hpoint.comp (line_isometry A c).injective)
    (linear p q / 2) ((leading p q - constant p q) / 2)
    (-(leading p q + constant p q) / 2) (normal_nonzero hpq)
    (fun u => bisector_mem_affineLine p q (line A c u) (line_bisector A c u)) s t

theorem metricSegment_eq_line_interval (A : SL2) (c s t : ℝ) :
    metricSegment (line A c s) (line A c t) = line A c '' uIcc s t := by
  rw [← range_segment]
  apply Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨clock s t v, clock_between s t v, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨v, hv⟩ := exists_clock s t u hu
    exact ⟨v, by change line A c (clock s t v) = line A c u; rw [hv]⟩

theorem image_metricSegment (a b : ℍ) :
    point '' metricSegment a b = segment ℝ (point a) (point b) := by
  obtain ⟨A, c, s, t, hs, ht⟩ := exists_clock_coordinates a b
  change line A c s = a at hs
  change line A c t = b at ht
  rw [← hs, ← ht, metricSegment_eq_line_interval, image_image]
  exact image_line_interval A c s t

theorem mem_metricSegment_iff (a b z : ℍ) :
    z ∈ metricSegment a b ↔ point z ∈ segment ℝ (point a) (point b) := by
  rw [← image_metricSegment]
  constructor
  · exact mem_image_of_mem point
  · rintro ⟨w, hw, he⟩
    have hwz : w = z := homeomorph.injective (Subtype.ext he)
    exact hwz ▸ hw

theorem interpolate_mem_metricSegment (a b : ℍ) (t : I) :
    HyperbolicKleinSegments.interpolate a b t ∈ metricSegment a b := by
  rw [mem_metricSegment_iff, HyperbolicKleinSegments.point_interpolate]
  exact ⟨1 - t.val, t.val, sub_nonneg.mpr t.property.2, t.property.1, by ring, rfl⟩

end VeechDichotomy.HyperbolicKleinGeodesics
