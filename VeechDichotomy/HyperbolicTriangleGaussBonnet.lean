module

public import VeechDichotomy.NormalizedIntrinsicTriangleAngles

/-! Gauss--Bonnet for every actual noncollinear finite hyperbolic
triangle, using the fixed intrinsic endpoint-angle function. Actual
vertex-set normalization and proved permutation invariance remove all
normal-form choices from the statement. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicTriangleGaussBonnet

open LinearGroup Set MeasureTheory HyperbolicTripleNormalization HyperbolicTriangles
open HyperbolicIntrinsicAngles FiniteTriangleNormalization
open scoped UpperHalfPlane ENNReal

theorem first_ne_second {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) : a ≠ b := by
  intro he
  obtain ⟨A, ha, hc⟩ := pair_axis a c
  exact h ⟨A, 0, ha, he ▸ ha, hc⟩

theorem second_ne_last {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) : b ≠ c := by
  intro he
  obtain ⟨A, ha, hb⟩ := pair_axis a b
  exact h ⟨A, 0, ha, hb, he ▸ hb⟩

theorem triple_permutation {α : Type*} (a b c x y z : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hset : ({a, b, c} : Set α) = {x, y, z}) :
    (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
      (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
      (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x) := by
  have ha : a = x ∨ a = y ∨ a = z := by
    have hm : a ∈ ({a, b, c} : Set α) := by simp
    rw [hset] at hm
    simpa only [mem_insert_iff, mem_singleton_iff] using hm
  have hb : b = x ∨ b = y ∨ b = z := by
    have hm : b ∈ ({a, b, c} : Set α) := by simp
    rw [hset] at hm
    simpa only [mem_insert_iff, mem_singleton_iff] using hm
  have hc : c = x ∨ c = y ∨ c = z := by
    have hm : c ∈ ({a, b, c} : Set α) := by simp
    rw [hset] at hm
    simpa only [mem_insert_iff, mem_singleton_iff] using hm
  grind

theorem angleSum_congr_set {a b c x y z : ℍ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hset : ({a, b, c} : Set ℍ) = {x, y, z}) : angleSum a b c = angleSum x y z := by
  rcases triple_permutation a b c x y z hab hac hbc hset with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first | rfl | (unfold angleSum; simp only [angleAt_comm]; ring)

theorem real_area_noncollinear {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) :
    (volume (triangle a b c)).toReal = Real.pi - angleSum a b c := by
  obtain ⟨M, x, y, hx, hy, hxy, p, hpre, hp, hvertices⟩ := exists_model_vertices h
  have htriangle : triangle a b c = triangle (M • MobiusIdealTriangleArea.vertex x hx (hxy.trans hy))
      (M • MobiusIdealTriangleArea.vertex y (hx.trans hxy) hy) (M • p) := by
    change HyperbolicGeodesicHulls.hull _ = HyperbolicGeodesicHulls.hull _
    rw [hvertices]
  rw [htriangle, angleSum_congr_set (first_ne_second h) (first_ne_last h) (second_ne_last h) hvertices]
  exact NormalizedIntrinsicTriangleAngles.mapped_real_area_formula M hx hy hxy p hpre hp

theorem angle_sum_le_pi {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) : angleSum a b c ≤ Real.pi := by
  have hn := ENNReal.toReal_nonneg (a := volume (triangle a b c))
  rw [real_area_noncollinear h] at hn
  linarith

theorem area_noncollinear {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) :
    volume (triangle a b c) = ENNReal.ofReal (Real.pi - angleSum a b c) := by
  rw [← real_area_noncollinear h, ENNReal.ofReal_toReal (area_triangle_lt_top a b c).ne]

end VeechDichotomy.HyperbolicTriangleGaussBonnet
