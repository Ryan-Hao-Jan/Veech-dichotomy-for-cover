module

public import VeechDichotomy.NativeHorizontalSlices

/-! Geometric intersection counts with opposite native vertical
segments. Hit-time counts are proved equal to geometric counts for
an embedded horizontal arc. Finiteness and the at-most-one discrepancy
are consequences of the actual flow, not additional count assumptions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRectangleCrossings

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSlices
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

def crossings (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ) : Set (Regular q) :=
  slice q i c J ∩ trajectory q horizontal x '' Icc a z

def crossingCount (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ) : ℕ :=
  (crossings q i x c J a z).ncard

theorem crossings_eq_image (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ)
    (hI : Icc a z ⊆ domain q horizontal x) :
    crossings q i x c J a z = trajectory q horizontal x '' (hits q i x c J ∩ Icc a z) := by
  ext y
  constructor
  · rintro ⟨hy, t, ht, rfl⟩
    exact ⟨t, ⟨⟨hI ht, hy⟩, ht⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht.1.2, t, ht.2, rfl⟩

theorem finite_crossings {l r b u c : ℝ} (hc : c ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    (x : Regular q) (a z : ℝ) (hI : Icc a z ⊆ domain q horizontal x) :
    (crossings q i x c J a z).Finite := by
  have hd : (c + r) / 2 ∈ Ioo l r := by constructor <;> linarith [hc.1, hc.2]
  have hw : 0 < (c + r) / 2 - c := by linarith [hc.2]
  rw [crossings_eq_image q i x c J a z hI]
  exact (SeparatedWindowCounts.finite_window hw (hits_separated q i hc hd hR hJ x) a z).image _

theorem crossingCount_eq (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ)
    (hI : Icc a z ⊆ domain q horizontal x) (hinj : InjOn (trajectory q horizontal x) (Icc a z)) :
    crossingCount q i x c J a z = SeparatedWindowCounts.count (hits q i x c J) a z := by
  unfold crossingCount SeparatedWindowCounts.count
  rw [crossings_eq_image q i x c J a z hI]
  exact (hinj.mono inter_subset_right).ncard_image

theorem count_bounds {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r) (hcd : c < d)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    (x : Regular q) (a z : ℝ) (hI : Icc a z ⊆ domain q horizontal x)
    (hinj : InjOn (trajectory q horizontal x) (Icc a z)) :
    crossingCount q i x c J a z ≤ crossingCount q i x d J a z + 1 ∧
      crossingCount q i x d J a z ≤ crossingCount q i x c J a z + 1 := by
  rw [crossingCount_eq q i x c J a z hI hinj, crossingCount_eq q i x d J a z hI hinj]
  exact NativeHorizontalSlices.count_bounds q i hc hd hcd hR hJ x a z

theorem closed_segment_count_bounds {l r b u c d v w : ℝ}
    (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r) (hcd : c < d)
    (hv : b < v) (hw : w < u) (hR : rectangle l r b u ⊆ (chart q i).target)
    (x : Regular q) (a z : ℝ) (hI : Icc a z ⊆ domain q horizontal x)
    (hinj : InjOn (trajectory q horizontal x) (Icc a z)) :
    crossingCount q i x c (Icc v w) a z ≤ crossingCount q i x d (Icc v w) a z + 1 ∧
      crossingCount q i x d (Icc v w) a z ≤ crossingCount q i x c (Icc v w) a z + 1 := by
  apply count_bounds q i hc hd hcd hR _ x a z hI hinj
  intro t ht
  exact ⟨hv.trans_le ht.1, ht.2.trans_lt hw⟩

end VeechDichotomy.NativeRectangleCrossings
