module

public import VeechDichotomy.HyperbolicEndpointTangents

/-! The fixed, intrinsic endpoint-angle function equals all three actual
boundary tangent angles of the normalized finite triangle. Actual circle
incidences and vertical height ordering prove positive scalar factors,
so the already measured area is pi minus this fixed intrinsic angle sum. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIntrinsicTriangleAngles

open LinearGroup MeasureTheory HyperbolicTriangles MobiusIdealTriangleArea
open NormalizedFiniteTriangleArea NormalizedFiniteTriangleParameters NormalizedFiniteTriangleAngles
open HyperbolicDirectionVectors HyperbolicIntrinsicAngles HyperbolicEndpointTangents
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

theorem vertex_re (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) : (vertex x hx₀ hx₁).re = x := by
  simp [vertex, NormalizedTriangleTangents.curve]

theorem unit_tangent (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    circleTangent 0 (vertex x hx₀ hx₁) = NormalizedTriangleTangents.leftTangent x := by
  apply Complex.ext <;>
    simp [circleTangent, vertex, NormalizedTriangleTangents.curve, NormalizedTriangleTangents.leftTangent]

theorem upper_height_gt {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) (p : ℍ)
    (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) : (vertex a ha₀ ha₁).im < p.im := by
  have hunit := unit_vertex_normSq a ha₀ ha₁
  have hreal : p.re = (vertex a ha₀ ha₁).re := by rw [vertex_re, hpre]
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hunit hp
  rw [hreal] at hp
  nlinarith [(vertex a ha₀ ha₁).im_pos, p.im_pos]

theorem lower_corner {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    angleAt (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p = lowerAngle a := by
  let A := vertex a ha (hab.trans hb)
  let B := vertex b (ha.trans hab) hb
  have hA : Complex.normSq ((A : ℂ) - (0 : ℂ)) = (1 : ℝ) ^ 2 := by
    simpa only [sub_zero, one_pow] using unit_vertex_normSq a ha (hab.trans hb)
  have hB : Complex.normSq ((B : ℂ) - (0 : ℂ)) = (1 : ℝ) ^ 2 := by
    simpa only [sub_zero, one_pow] using unit_vertex_normSq b (ha.trans hab) hb
  obtain ⟨k, hk, hAB⟩ := circle_right 0 1 A B hA hB (by simpa only [A, B, vertex_re] using hab)
  obtain ⟨l, hl, hAP⟩ := vertical_up A p (by simp only [A, vertex_re, hpre])
    (upper_height_gt ha (hab.trans hb) p hpre hp)
  change InnerProductGeometry.angle (direction A B) (direction A p) = _
  rw [hAB, hAP, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl, unit_tangent]
  exact InnerProductGeometry.angle_comm _ _

theorem upper_corner {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    angleAt p (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) = upperAngle a b p := by
  let A := vertex a ha (hab.trans hb)
  let B := vertex b (ha.trans hab) hb
  obtain ⟨k, hk, hPA⟩ := vertical_down p A (by simp only [A, vertex_re, hpre])
    (upper_height_gt ha (hab.trans hb) p hpre hp)
  obtain ⟨l, hl, hPB⟩ := circle_right (center a b p) (radius a b p) p B
    (circle_incidence a b p) (right_circle_incidence ha hb hab p hpre)
    (by simpa only [B, vertex_re, hpre] using hab)
  have htan : circleTangent (center a b p) p =
      CircularTriangleTangents.rightwardTangent (center a b p) (radius a b p) a := by
    have h := circleTangent_graph (center a b p) (radius a b p) p (circle_incidence a b p)
    rwa [hpre] at h
  change InnerProductGeometry.angle (direction p A) (direction p B) = _
  rw [hPA, hPB, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl, htan]
  rfl

theorem right_corner {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) :
    angleAt (vertex b (ha.trans hab) hb) (vertex a ha (hab.trans hb)) p = rightAngle a b p := by
  let A := vertex a ha (hab.trans hb)
  let B := vertex b (ha.trans hab) hb
  have hA : Complex.normSq ((A : ℂ) - (0 : ℂ)) = (1 : ℝ) ^ 2 := by
    simpa only [sub_zero, one_pow] using unit_vertex_normSq a ha (hab.trans hb)
  have hB : Complex.normSq ((B : ℂ) - (0 : ℂ)) = (1 : ℝ) ^ 2 := by
    simpa only [sub_zero, one_pow] using unit_vertex_normSq b (ha.trans hab) hb
  obtain ⟨k, hk, hBA⟩ := circle_left 0 1 B A hB hA (by simpa only [A, B, vertex_re] using hab)
  obtain ⟨l, hl, hBP⟩ := circle_left (center a b p) (radius a b p) B p
    (right_circle_incidence ha hb hab p hpre) (circle_incidence a b p)
    (by simpa only [B, vertex_re, hpre] using hab)
  have htan : circleTangent (center a b p) B =
      CircularTriangleTangents.rightwardTangent (center a b p) (radius a b p) b := by
    simpa only [B, vertex_re] using circleTangent_graph (center a b p) (radius a b p) B
      (right_circle_incidence ha hb hab p hpre)
  change InnerProductGeometry.angle (direction B A) (direction B p) = _
  rw [hBA, hBP, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl, unit_tangent, htan]
  rfl

theorem real_area_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p)).toReal =
      Real.pi - angleSum (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p := by
  rw [angleSum, lower_corner ha hb hab p hpre hp, right_corner ha hb hab p hpre,
    upper_corner ha hb hab p hpre hp]
  exact NormalizedFiniteTriangleAngles.real_area_angles ha hb hab p hpre hp

theorem mapped_real_area_formula (M : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (M • vertex a ha (hab.trans hb)) (M • vertex b (ha.trans hab) hb) (M • p))).toReal =
      Real.pi - angleSum (M • vertex a ha (hab.trans hb)) (M • vertex b (ha.trans hab) hb) (M • p) := by
  rw [angleSum_smul, ← image_triangle_smul]
  have hm : volume ((fun z : ℍ => M • z) '' triangle (vertex a ha (hab.trans hb))
      (vertex b (ha.trans hab) hb) p) = volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p) :=
    measure_smul (volume : Measure ℍ) M _
  rw [hm]
  exact real_area_formula ha hb hab p hpre hp

end VeechDichotomy.NormalizedIntrinsicTriangleAngles
