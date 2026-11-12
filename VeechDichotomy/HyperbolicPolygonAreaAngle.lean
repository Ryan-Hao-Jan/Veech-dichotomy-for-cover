module

public import VeechDichotomy.HyperbolicPolygonAngles

/-! The actual area-angle formula and total exterior-angle budget for
strictly ordered finite hyperbolic polygons. The region is its literal
intrinsic hull, its actual fan triangulation and corner additions have
been proved, and comparison with a containing finite-area convex region
gives the genuine geometric deficit bound needed for Dirichlet domains. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicPolygonAreaAngle

open Set MeasureTheory HyperbolicPolygonFans HyperbolicPolygonAngles StrictKleinPolygons
open HyperbolicGeodesicHulls HyperbolicIntrinsicAngles
open scoped UpperHalfPlane ENNReal

theorem real_area_formula (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    (volume (polygon a v n)).toReal = (n : ℝ) * Real.pi - polygonAngleSum a v n := by
  rw [HyperbolicFanAreas.real_area_angle_sum a v n hn h.1 (supportingEdges h), fan_angle_sum a v n hn h]

theorem area_formula (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    volume (polygon a v n) = ENNReal.ofReal ((n : ℝ) * Real.pi - polygonAngleSum a v n) := by
  rw [← real_area_formula a v n hn h, ENNReal.ofReal_toReal (area_polygon_lt_top a v n).ne]

def exteriorSum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : ℝ :=
  (Real.pi - angleAt a (v 0) (v n)) + (Real.pi - angleAt (v 0) a (v 1)) +
    (∑ i ∈ Finset.range (n - 1), (Real.pi - angleAt (v (i + 1)) (v i) (v (i + 2)))) +
    (Real.pi - angleAt (v n) a (v (n - 1)))

theorem exterior_formula (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) :
    exteriorSum a v n = ((n : ℝ) + 2) * Real.pi - polygonAngleSum a v n := by
  simp only [exteriorSum, polygonAngleSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ n from hn), Nat.cast_one]
  ring

theorem exterior_nonneg (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : 0 ≤ exteriorSum a v n := by
  unfold exteriorSum
  exact add_nonneg (add_nonneg (add_nonneg (sub_nonneg.mpr (angleAt_le_pi _ _ _))
    (sub_nonneg.mpr (angleAt_le_pi _ _ _)))
      (Finset.sum_nonneg (fun _ _ => sub_nonneg.mpr (angleAt_le_pi _ _ _))))
    (sub_nonneg.mpr (angleAt_le_pi _ _ _))

theorem exterior_area (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    exteriorSum a v n = (volume (polygon a v n)).toReal + 2 * Real.pi := by
  rw [exterior_formula a v n hn, real_area_formula a v n hn h]
  ring

theorem exterior_bound (S : Set ℍ) (hS : GeodesicallyConvex S) (hfinite : volume S ≠ ⊤)
    (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n)
    (ha : a ∈ S) (hv : ∀ i : ℕ, i ≤ n → v i ∈ S) :
    exteriorSum a v n ≤ (volume S).toReal + 2 * Real.pi := by
  rw [exterior_area a v n hn h]
  have harea := ENNReal.toReal_mono hfinite
    (measure_mono (HyperbolicFanAreas.polygon_subset hS a v n ha hv))
  linarith only [harea]

end VeechDichotomy.HyperbolicPolygonAreaAngle
