module

public import VeechDichotomy.NativeHorizontalSlices

/-! A closed vertical chart slice is exactly an actual native vertical
trajectory segment based at any point on the same line. This identifies
the rectangle sides used in intersection comparison with actual orbit
segments, including backward segments at an upper endpoint. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeVerticalSlices

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSlices NativeHorizontalSides
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

theorem segment_domain {l r b u c v w : ℝ} (hc : c ∈ Ioo l r) (hv : b < v) (hw : w < u)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) (hx : x ∈ side q i c b u) :
    Icc (v - (chart q i x).2) (w - (chart q i x).2) ⊆ domain q vertical x := by
  have hxr : chart q i x ∈ rectangle l r b u := ⟨hx.2.1.symm ▸ hc, hx.2.2⟩
  intro t ht
  apply (vertical_interval q i hR x hx.1 hxr).1
  constructor <;> linarith [ht.1, ht.2]

theorem slice_eq_segment {l r b u c v w : ℝ} (hc : c ∈ Ioo l r) (hv : b < v) (hw : w < u)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) (hx : x ∈ side q i c b u) :
    slice q i c (Icc v w) = trajectory q vertical x '' Icc (v - (chart q i x).2) (w - (chart q i x).2) := by
  have hxr : chart q i x ∈ rectangle l r b u := ⟨hx.2.1.symm ▸ hc, hx.2.2⟩
  have hseg := vertical_interval q i hR x hx.1 hxr
  ext y
  constructor
  · intro hy
    let τ := (chart q i y).2 - (chart q i x).2
    have hτ : τ ∈ Icc (v - (chart q i x).2) (w - (chart q i x).2) := by
      constructor <;> linarith [hy.2.2.1, hy.2.2.2]
    have hτo : τ ∈ Ioo (b - (chart q i x).2) (u - (chart q i x).2) := by
      constructor <;> linarith [hτ.1, hτ.2]
    refine ⟨τ, hτ, ?_⟩
    rw [hseg.2 τ hτo]
    have hp : ((chart q i x).1, (chart q i x).2 + τ) = chart q i y := by
      apply Prod.ext
      · exact hx.2.1.trans hy.2.1.symm
      · dsimp only [τ]; ring
    rw [hp, (chart q i).left_inv hy.1]
  · rintro ⟨τ, hτ, rfl⟩
    have hτo : τ ∈ Ioo (b - (chart q i x).2) (u - (chart q i x).2) := by
      constructor <;> linarith [hτ.1, hτ.2]
    have htarget : ((chart q i x).1, (chart q i x).2 + τ) ∈ (chart q i).target := by
      apply hR
      exact ⟨hxr.1, by constructor <;> linarith [hτ.1, hτ.2]⟩
    rw [hseg.2 τ hτo]
    have hp := (chart q i).right_inv htarget
    refine ⟨(chart q i).map_target htarget, ?_, ?_⟩
    · simpa only [hp] using hx.2.1
    · simpa only [hp] using (show (chart q i x).2 + τ ∈ Icc v w from
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)

end VeechDichotomy.NativeVerticalSlices
