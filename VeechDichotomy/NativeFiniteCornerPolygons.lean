module

public import VeechDichotomy.FiniteRealKeyEnumeration

/-! Every finite set of at least three actual Dirichlet corners has an
actual strictly convex cyclic vertex enumeration. The root's exposing
functional gives injective real slope keys, whose proved finite ordering
constructs the genuine polygon. The native lattice then bounds its actual
total exterior angle deficit, with no ordering hypothesis left to assume. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFiniteCornerPolygons

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicPolygonFans StrictKleinPolygons DirichletCornerSlopeOrder HyperbolicKleinMap
open HyperbolicPolygonAngles HyperbolicPolygonAreaAngle HyperbolicGeodesicHulls
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

theorem enumerate (Γ : Subgroup SL2) (p : ℍ) (S : Finset ℍ)
    (hS : ∀ z ∈ S, z ∈ corners Γ p) (hcard : 3 ≤ S.card) :
    ∃ (a : ℍ) (v : ℕ → ℍ) (n : ℕ), a ∈ S ∧ 0 < n ∧ n + 2 = S.card ∧
      vertices a v n = (S : Set ℍ) ∧ StrictlyOrdered a v n := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨L, hL, hinj⟩ := exists_key Γ p a (hS a ha)
  let T := S.erase a
  have hTset : (T : Set ℍ) ⊆ corners Γ p \ {a} := by
    intro z hz
    have hm := Finset.mem_erase.mp hz
    exact ⟨hS z hm.2, by simpa only [mem_singleton_iff] using hm.1⟩
  have hTinj : InjOn (key L a) (T : Set ℍ) := fun _ hu _ hv he => hinj (hTset hu) (hTset hv) he
  obtain ⟨v, hmem, himage, hkeys⟩ := FiniteRealKeyEnumeration.enumerate T (key L a) hTinj a
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem ha
  let n := T.card - 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hncard : n + 1 = T.card := Nat.sub_add_cancel (show 1 ≤ T.card by omega)
  have hcount : n + 2 = S.card := by omega
  have hinterval : (Iic n : Set ℕ) = Iio T.card := by
    ext i
    simp only [mem_Iic, mem_Iio]
    omega
  have hrest : v '' Iic n = (T : Set ℍ) := by rw [hinterval]; exact himage
  have hvertices : vertices a v n = (S : Set ℍ) := by
    rw [vertices, hrest]
    have hs := congrArg (fun U : Finset ℍ => (U : Set ℍ)) (Finset.insert_erase ha)
    simpa only [Finset.coe_insert] using hs
  have hvCorner : ∀ i : ℕ, i ≤ n → v i ∈ corners Γ p := by
    intro i hi
    exact (hTset (hmem i (by omega))).1
  have horder : OrderedRays a v n := by
    intro i j hij hj
    have hii : i < T.card := by omega
    have hjj : j < T.card := by omega
    have hvi := hTset (hmem i hii)
    have hvj := hTset (hmem j hjj)
    exact key_lt_orient Γ p a L hL (v i) (v j) hvi.1.1 hvj.1.1
      (by simpa only [mem_singleton_iff] using hvi.2)
      (by simpa only [mem_singleton_iff] using hvj.2) (hkeys i j hij hjj)
  exact ⟨a, v, n, ha, hn, hcount, hvertices,
    DirichletCornerPolygonOrder.strictlyOrdered Γ p a v n (hS a ha).1 hvCorner horder⟩

theorem area_and_deficit (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (S : Finset ℍ)
    (hS : ∀ z ∈ S, z ∈ corners Γ p) (hcard : 3 ≤ S.card) :
    ∃ (a : ℍ) (v : ℕ → ℍ) (n : ℕ), 0 < n ∧ n + 2 = S.card ∧ vertices a v n = (S : Set ℍ) ∧
      StrictlyOrdered a v n ∧ (volume (hull (S : Set ℍ))).toReal =
        (n : ℝ) * Real.pi - polygonAngleSum a v n ∧
      exteriorSum a v n ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  classical
  obtain ⟨a, v, n, ha, hn, hcount, hvertices, hstrict⟩ := enumerate Γ p S hS hcard
  have hpoly : polygon a v n = hull (S : Set ℍ) := by rw [polygon, hvertices]
  have hvD : ∀ i : ℕ, i ≤ n → v i ∈ region Γ p := by
    intro i hi
    have hm : v i ∈ vertices a v n := Or.inr ⟨i, hi, rfl⟩
    rw [hvertices] at hm
    exact (hS (v i) hm).1
  refine ⟨a, v, n, hn, hcount, hvertices, hstrict, ?_, ?_⟩
  · rw [← hpoly]
    exact HyperbolicPolygonAreaAngle.real_area_formula a v n hn hstrict
  · exact NativeDirichletPolygonDeficit.exterior_bound Γ hΓ p a v n hn hstrict (hS a ha).1 hvD

end VeechDichotomy.NativeFiniteCornerPolygons
