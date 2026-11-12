module

public import VeechDichotomy.VerticalTriangleStandardization
public import VeechDichotomy.MobiusFiniteTriangleAngles

/-! Every actual noncollinear hyperbolic triple, as an unordered vertex
set, is an actual SL2 image of the finite triangle model. The normalization
matrices, endpoint order and circle parameters are constructed by the
preceding actual geometric proofs, not assumed as a normal-form interface. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteTriangleNormalization

open LinearGroup Set HyperbolicTripleNormalization HyperbolicGeodesicHulls HyperbolicTriangles
open MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem exists_model_vertices {x y z : ℍ} (h : ¬OnCommonGeodesic x y z) :
    ∃ (M : SL2) (a b : ℝ) (ha : -1 < a) (hb : b < 1) (hab : a < b) (p : ℍ),
      p.re = a ∧ 1 < Complex.normSq (p : ℂ) ∧
        ({x, y, z} : Set ℍ) = {M • vertex a ha (hab.trans hb), M • vertex b (ha.trans hab) hb, M • p} := by
  obtain ⟨A, u, v, w, hset, hvertical, hheight, hright⟩ := exists_vertical_right h
  obtain ⟨F, a, b, ha, hb, hab, p, hu, hv, hw, hpre, hp⟩ :=
    VerticalTriangleStandardization.exists_model u v w hvertical hheight hright
  let B := F * A
  have hglobal : (fun q : ℍ => B • q) '' {x, y, z} =
      {vertex a ha (hab.trans hb), vertex b (ha.trans hab) hb, p} := by
    calc
      _ = (fun q : ℍ => F • q) '' ((fun q : ℍ => A • q) '' {x, y, z}) := by
        simp only [B, image_image, mul_smul]
      _ = (fun q : ℍ => F • q) '' {u, v, w} := by rw [← hset]
      _ = _ := by simp only [image_insert_eq, image_singleton, hu, hv, hw]
  have hinv := congrArg (fun S : Set ℍ => (fun q : ℍ => B⁻¹ • q) '' S) hglobal
  simp only [inv_smul_smul, image_insert_eq, image_singleton] at hinv
  exact ⟨B⁻¹, a, b, ha, hb, hab, p, hpre, hp, hinv⟩

theorem exists_model {x y z : ℍ} (h : ¬OnCommonGeodesic x y z) :
    ∃ (M : SL2) (a b : ℝ) (ha : -1 < a) (hb : b < 1) (hab : a < b) (p : ℍ),
      p.re = a ∧ 1 < Complex.normSq (p : ℂ) ∧
        triangle x y z = triangle (M • vertex a ha (hab.trans hb)) (M • vertex b (ha.trans hab) hb) (M • p) := by
  obtain ⟨M, a, b, ha, hb, hab, p, hpre, hp, hvertices⟩ := exists_model_vertices h
  refine ⟨M, a, b, ha, hb, hab, p, hpre, hp, ?_⟩
  change hull {x, y, z} = hull {M • vertex a ha (hab.trans hb), M • vertex b (ha.trans hab) hb, M • p}
  rw [hvertices]

end VeechDichotomy.FiniteTriangleNormalization
