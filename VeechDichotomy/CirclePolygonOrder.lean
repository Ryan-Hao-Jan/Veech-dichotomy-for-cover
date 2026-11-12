module

public import VeechDichotomy.PlanarPolygonAngles

/-! Every actual finite set of at least three equal-radius nonzero
complex points has a constructed strict cyclic polygon order. Actual
exposing functionals and injective real slope keys supply the enumeration;
an inward turn would put a circle point in the hull of the others. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CirclePolygonOrder

open Set ComplexOrientedTriangles PlanarPolygonAngles

set_option backward.isDefEq.respectTransparency false

theorem positiveTriples (V : Set ℂ) (R : ℝ) (hV : ∀ z ∈ V, ‖z‖ = R)
    (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (ha : a ∈ V) (hv : ∀ i : ℕ, i ≤ n → v i ∈ V)
    (horder : OrderedPlanarFans.OrderedRays a v n) : PositiveTriples v n := by
  intro i j k hij hjk hk
  have hj : j ≤ n := hjk.le.trans hk
  have hi : i ≤ n := hij.le.trans hj
  have h₁ := PlanarFanIntersections.positive_distinct (horder i j hij hj)
  have h₂ := PlanarFanIntersections.positive_distinct (horder j k hjk hk)
  have hmem (z : ℂ) (hz : z ∈ V) (hne : z ≠ v j) : z ∈ V \ {v j} :=
    ⟨hz, by simpa only [mem_singleton_iff] using hne⟩
  have hsub : ({a, v i, v k} : Set ℂ) ⊆ V \ {v j} := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hmem a ha h₁.2.1, hmem (v i) (hv i hi) h₁.2.2, hmem (v k) (hv k hk) h₂.2.2.symm⟩
  by_contra hn
  have hnon : orient (v i) (v j) (v k) ≤ 0 := le_of_not_gt hn
  have hmid : 0 ≤ orient (v i) (v k) (v j) := by
    rw [orient_swap (v i) (v k) (v j), orient_rotate (v k) (v i) (v j)]
    exact neg_nonneg.mpr hnon
  have hlast : 0 ≤ orient (v k) a (v j) := by rw [orient_rotate]; exact (horder j k hjk hk).le
  have htri : v j ∈ OrientedTriangleRegions.region a (v i) (v k) :=
    (OrientedTriangleRegions.mem_iff _ _ _ _ (horder i k (hij.trans hjk) hk)).mpr
      ⟨(horder i j hij hj).le, hmid, hlast⟩
  exact CircleExposedPoints.not_mem_hull_rest V R hV (v j) (hv j hj) (convexHull_mono hsub htri)

theorem enumerate (S : Finset ℂ) (R : ℝ) (hR : 0 < R) (hS : ∀ z ∈ S, ‖z‖ = R) (hcard : 3 ≤ S.card) :
    ∃ (a : ℂ) (v : ℕ → ℂ) (n : ℕ), a ∈ S ∧ 0 < n ∧ n + 2 = S.card ∧
      OrderedPlanarFans.vertices a v n = (S : Set ℂ) ∧ StrictlyOrdered a v n := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let L := CircleExposedPoints.functional a
  have hLne : L ≠ 0 := CircleExposedPoints.functional_ne_zero a R (hS a ha) hR
  have hinj := CircleExposedPoints.slope_injective (S : Set ℂ) R hR hS a ha
  let T := S.erase a
  have hTset : (T : Set ℂ) ⊆ (S : Set ℂ) \ {a} := by
    intro z hz
    have hm := Finset.mem_erase.mp hz
    exact ⟨hm.2, by simpa only [mem_singleton_iff] using hm.1⟩
  have hTinj : InjOn (ExposedRootCoordinates.slope L a) (T : Set ℂ) :=
    fun _ hu _ hv he => hinj (hTset hu) (hTset hv) he
  obtain ⟨v, hmem, himage, hkeys⟩ := FiniteRealKeyEnumeration.enumerate T (ExposedRootCoordinates.slope L a) hTinj a
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem ha
  let n := T.card - 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hncard : n + 1 = T.card := Nat.sub_add_cancel (show 1 ≤ T.card by omega)
  have hcount : n + 2 = S.card := by omega
  have hinterval : (Iic n : Set ℕ) = Iio T.card := by ext i; simp only [mem_Iic, mem_Iio]; omega
  have hrest : v '' Iic n = (T : Set ℂ) := by rw [hinterval]; exact himage
  have hvertices : OrderedPlanarFans.vertices a v n = (S : Set ℂ) := by
    rw [OrderedPlanarFans.vertices, hrest]
    have hs := congrArg (fun U : Finset ℂ => (U : Set ℂ)) (Finset.insert_erase ha)
    simpa only [Finset.coe_insert] using hs
  have hvS : ∀ i : ℕ, i ≤ n → v i ∈ S := by
    intro i hi
    exact Finset.mem_of_mem_erase (hmem i (by omega))
  have horder : OrderedPlanarFans.OrderedRays a v n := by
    intro i j hij hj
    have hii : i < T.card := by omega
    have hjj : j < T.card := by omega
    have hvi := Finset.mem_erase.mp (hmem i hii)
    have hvj := Finset.mem_erase.mp (hmem j hjj)
    exact ExposedRootCoordinates.slope_lt_orient L hLne a (v i) (v j)
      (CircleExposedPoints.exposing_pair a (v i) R (hS a ha) (hS (v i) hvi.2) hvi.1)
      (CircleExposedPoints.exposing_pair a (v j) R (hS a ha) (hS (v j) hvj.2) hvj.1)
      (hkeys i j hij hjj)
  exact ⟨a, v, n, ha, hn, hcount, hvertices, horder,
    positiveTriples (S : Set ℂ) R hS a v n ha hvS horder⟩

end VeechDichotomy.CirclePolygonOrder
