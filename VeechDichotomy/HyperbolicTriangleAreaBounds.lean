module

public import VeechDichotomy.CollinearHyperbolicTriangles

/-! Actual area bounds for every finite hyperbolic triangle. Common-line
triples have zero area; every other triple has the constructed finite
normal form and actual positive tangent angles, so its real area is
strictly less than pi. The normal form's angle identity is also exported
for arbitrary noncollinear triples with the actual vertex-set witness. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicTriangleAreaBounds

open LinearGroup Set MeasureTheory HyperbolicTriangles HyperbolicTripleNormalization
open FiniteTriangleNormalization MobiusIdealTriangleArea
open scoped UpperHalfPlane ENNReal

theorem normalized_area_lt_pi (M : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (M • vertex a ha (hab.trans hb)) (M • vertex b (ha.trans hab) hb) (M • p))).toReal <
      Real.pi := by
  rw [MobiusFiniteTriangleAngles.real_area_angles M ha hb hab p hpre hp,
    MobiusFiniteTriangleAngles.lowerImageAngle_eq, MobiusFiniteTriangleAngles.rightImageAngle_eq,
    MobiusFiniteTriangleAngles.upperImageAngle_eq]
  have hl := NormalizedFiniteTriangleAngles.lowerAngle_pos ha (hab.trans hb)
  have hr := NormalizedFiniteTriangleAngles.rightAngle_pos ha hb hab p hpre hp
  have hu := NormalizedFiniteTriangleAngles.upperAngle_pos ha hb hab p hpre
  linarith

theorem real_area_lt_pi (x y z : ℍ) : (volume (triangle x y z)).toReal < Real.pi := by
  by_cases h : OnCommonGeodesic x y z
  · rw [CollinearHyperbolicTriangles.real_area_zero h]
    exact Real.pi_pos
  · obtain ⟨M, a, b, ha, hb, hab, p, hpre, hp, htriangle⟩ := exists_model h
    rw [htriangle]
    exact normalized_area_lt_pi M ha hb hab p hpre hp

theorem area_lt_pi (x y z : ℍ) : volume (triangle x y z) < ENNReal.ofReal Real.pi := by
  have hfin := (area_triangle_lt_top x y z).ne
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.mpr (real_area_lt_pi x y z)

theorem exists_angle_formula {x y z : ℍ} (h : ¬OnCommonGeodesic x y z) :
    ∃ (M : SL2) (a b : ℝ) (ha : -1 < a) (hb : b < 1) (hab : a < b) (p : ℍ),
      p.re = a ∧ 1 < Complex.normSq (p : ℂ) ∧
        ({x, y, z} : Set ℍ) = {M • vertex a ha (hab.trans hb), M • vertex b (ha.trans hab) hb, M • p} ∧
        (volume (triangle x y z)).toReal = Real.pi -
          (MobiusFiniteTriangleAngles.lowerImageAngle M a ha (hab.trans hb) +
            MobiusFiniteTriangleAngles.rightImageAngle M a b p (ha.trans hab) hb +
            MobiusFiniteTriangleAngles.upperImageAngle M a b p) := by
  obtain ⟨M, a, b, ha, hb, hab, p, hpre, hp, hvertices⟩ := exists_model_vertices h
  refine ⟨M, a, b, ha, hb, hab, p, hpre, hp, hvertices, ?_⟩
  have heq : triangle x y z =
      triangle (M • vertex a ha (hab.trans hb)) (M • vertex b (ha.trans hab) hb) (M • p) := by
    change HyperbolicGeodesicHulls.hull _ = HyperbolicGeodesicHulls.hull _
    rw [hvertices]
  rw [heq]
  exact MobiusFiniteTriangleAngles.real_area_angles M ha hb hab p hpre hp

end VeechDichotomy.HyperbolicTriangleAreaBounds
