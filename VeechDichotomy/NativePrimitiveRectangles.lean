module

public import VeechDichotomy.NativePrimitiveChartFlow
public import Mathlib.Tactic.Linarith

/-! Exact horizontal and vertical flow segments inside genuine native
primitive rectangles. Smaller rectangles have uniform flow times that
depend only on their physical dimensions, including for a varying fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePrimitiveRectangles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics Set Topology
open scoped Manifold ContDiff

def rectangle (l r b u : ℝ) : Set Plane := Ioo l r ×ˢ Ioo b u
def vertical : Plane := (0, 1)
def horizontal : Plane := (1, 0)

theorem add_vertical (p : Plane) (t : ℝ) : p + t • vertical = (p.1, p.2 + t) := by
  apply Prod.ext <;> simp [vertical]

theorem add_horizontal (p : Plane) (t : ℝ) : p + t • horizontal = (p.1 + t, p.2) := by
  apply Prod.ext <;> simp [horizontal]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem vertical_interval (i : Index q) {l r b u : ℝ}
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q)
    (hx : x ∈ (chart q i).source) (hxr : chart q i x ∈ rectangle l r b u) :
    Ioo (b - (chart q i x).2) (u - (chart q i x).2) ⊆ domain q vertical x ∧
      ∀ t ∈ Ioo (b - (chart q i x).2) (u - (chart q i x).2),
        trajectory q vertical x t = (chart q i).symm ((chart q i x).1, (chart q i x).2 + t) := by
  have hzero : (0 : ℝ) ∈ Ioo (b - (chart q i x).2) (u - (chart q i x).2) := by
    constructor <;> linarith [hxr.2.1, hxr.2.2]
  have hline : ∀ t ∈ Ioo (b - (chart q i x).2) (u - (chart q i x).2),
      chart q i x + t • vertical ∈ (chart q i).target := by
    intro t ht
    rw [add_vertical]
    exact hR ⟨hxr.1, by constructor <;> linarith [ht.1, ht.2]⟩
  simpa only [add_vertical] using NativePrimitiveChartFlow.interval_representation q i vertical x hx _
    isOpen_Ioo ordConnected_Ioo hzero hline

theorem horizontal_interval (i : Index q) {l r b u : ℝ}
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q)
    (hx : x ∈ (chart q i).source) (hxr : chart q i x ∈ rectangle l r b u) :
    Ioo (l - (chart q i x).1) (r - (chart q i x).1) ⊆ domain q horizontal x ∧
      ∀ t ∈ Ioo (l - (chart q i x).1) (r - (chart q i x).1),
        trajectory q horizontal x t = (chart q i).symm ((chart q i x).1 + t, (chart q i x).2) := by
  have hzero : (0 : ℝ) ∈ Ioo (l - (chart q i x).1) (r - (chart q i x).1) := by
    constructor <;> linarith [hxr.1.1, hxr.1.2]
  have hline : ∀ t ∈ Ioo (l - (chart q i x).1) (r - (chart q i x).1),
      chart q i x + t • horizontal ∈ (chart q i).target := by
    intro t ht
    rw [add_horizontal]
    exact hR ⟨by constructor <;> linarith [ht.1, ht.2], hxr.2⟩
  simpa only [add_horizontal] using NativePrimitiveChartFlow.interval_representation q i horizontal x hx _
    isOpen_Ioo ordConnected_Ioo hzero hline

theorem uniform_vertical_time (i : Index q) {W H : ℝ} (hH : 0 < H)
    (hR : rectangle (-W) W (-H) H ⊆ (chart q i).target) (x : Regular q)
    (hx : x ∈ (chart q i).source)
    (hxr : chart q i x ∈ rectangle (-W) W (-(H / 2)) (H / 2)) :
    ∀ t ∈ Ioo (-(H / 2)) (H / 2), t ∈ domain q vertical x ∧
      chart q i (trajectory q vertical x t) = ((chart q i x).1, (chart q i x).2 + t) := by
  have hfull : chart q i x ∈ rectangle (-W) W (-H) H :=
    ⟨hxr.1, by constructor <;> linarith [hxr.2.1, hxr.2.2]⟩
  have hseg := vertical_interval q i hR x hx hfull
  intro t ht
  have htime : t ∈ Ioo (-H - (chart q i x).2) (H - (chart q i x).2) := by
    constructor <;> linarith [hxr.2.1, hxr.2.2, ht.1, ht.2]
  refine ⟨hseg.1 htime, ?_⟩
  rw [hseg.2 t htime]
  apply (chart q i).right_inv
  exact hR ⟨hxr.1, by constructor <;> linarith [hxr.2.1, hxr.2.2, ht.1, ht.2]⟩

end VeechDichotomy.NativePrimitiveRectangles
