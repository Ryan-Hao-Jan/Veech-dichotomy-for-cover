module

public import MNEC.NativePrimitiveLineNull
public import MNEC.NativePartialDirectionalArea

@[expose] public section
noncomputable section

namespace MNEC.NativeCriticalRays

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativeRegularArea NativePrimitiveLineNull NativeDirectionalDynamics
open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

abbrev Zero (q : Differential X) := ↥(zeroSet q)

/-- Fixed per-zero data. Every field is constructed from the actual q,p
below. This record is never an input certificate to the null-union theorem. -/
structure Datum (q : Differential X) (p : Zero q) where
  U : Set X
  open_U : IsOpen U
  center : p.val ∈ U
  F : X → ℂ
  Fzero : F p.val = 0
  derivative : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y)
  continuous : ContinuousOn F U
  null_lines : ∀ a v : Plane, v ≠ 0 → regularArea q (linePreimage q U F a v) = 0

theorem datum_exists (q : Differential X) (p : Zero q) : Nonempty (Datum q p) := by
  obtain ⟨U, hU, hp, F, hFzero, hF, hcont, hnull⟩ := exists_local_primitive_with_null_lines q p.val
  exact ⟨⟨U, hU, hp, F, hFzero, hF, hcont, hnull⟩⟩

/-- Chosen ONCE from q,p; it does not depend on velocity or time. -/
def datum (q : Differential X) (p : Zero q) : Datum q p := Classical.choice (datum_exists q p)

@[instance_reducible] def zeroFintype (q : Differential X) : Fintype (Zero q) := (zeroSet_finite q).fintype

theorem zeros_countable (q : Differential X) : Countable (Zero q) := by
  let : Fintype (Zero q) := zeroFintype q
  infer_instance

def criticalLine (q : Differential X) (v : Plane) (p : Zero q) : Set (Regular q) :=
  linePreimage q (datum q p).U (datum q p).F 0 v

theorem mem_criticalLine_iff (q : Differential X) (v : Plane) (p : Zero q) (x : Regular q) :
    x ∈ criticalLine q v p ↔ x.val ∈ (datum q p).U ∧
      toPlane ((datum q p).F x.val) ∈ affineLine 0 v := Iff.rfl

theorem criticalLine_null (q : Differential X) (v : Plane) (hv : v ≠ 0) (p : Zero q) :
    regularArea q (criticalLine q v p) = 0 := (datum q p).null_lines 0 v hv

/-- A canonical measurable hull permits actual partial-area pullback
without requiring the literal primitive preimage to be Borel. -/
def criticalSet (q : Differential X) (v : Plane) (p : Zero q) : Set (Regular q) :=
  toMeasurable (regularArea q) (criticalLine q v p)

theorem criticalSet_measurable (q : Differential X) (v : Plane) (p : Zero q) :
    MeasurableSet (criticalSet q v p) := measurableSet_toMeasurable _ _

theorem criticalLine_subset_criticalSet (q : Differential X) (v : Plane) (p : Zero q) :
    criticalLine q v p ⊆ criticalSet q v p := subset_toMeasurable _ _

theorem criticalSet_null (q : Differential X) (v : Plane) (hv : v ≠ 0) (p : Zero q) :
    regularArea q (criticalSet q v p) = 0 := by
  rw [criticalSet, measure_toMeasurable]
  exact criticalLine_null q v hv p

theorem mem_criticalSet_of_value (q : Differential X) (v : Plane) (p : Zero q) (x : Regular q)
    (hxU : x.val ∈ (datum q p).U)
    (hxline : toPlane ((datum q p).F x.val) ∈ affineLine 0 v) : x ∈ criticalSet q v p :=
  criticalLine_subset_criticalSet q v p ⟨hxU, hxline⟩

def rationalHit (q : Differential X) (v : Plane) (p : Zero q) (a : ℚ) : Set (Regular q) :=
  {x | (a : ℝ) ∈ domain q v x ∧ trajectory q v x (a : ℝ) ∈ criticalSet q v p}

theorem mem_rationalHit_iff (q : Differential X) (v : Plane) (p : Zero q) (a : ℚ) (x : Regular q) :
    x ∈ rationalHit q v p a ↔ (a : ℝ) ∈ domain q v x ∧
      trajectory q v x (a : ℝ) ∈ criticalSet q v p := Iff.rfl

theorem rationalHit_measurable (q : Differential X) (v : Plane) (p : Zero q) (a : ℚ) :
    MeasurableSet (rationalHit q v p a) := by
  change MeasurableSet ((NativePartialDirectionalFlow.timeMap q v (a : ℝ)).source ∩
    NativePartialDirectionalFlow.timeMap q v (a : ℝ) ⁻¹' criticalSet q v p)
  exact (NativePartialDirectionalFlow.timeMap q v (a : ℝ)).open_source.measurableSet.inter
    ((criticalSet_measurable q v p).preimage (NativePartialDirectionalArea.measurable_timeMap q v (a : ℝ)))

theorem rationalHit_null (q : Differential X) (v : Plane) (hv : v ≠ 0) (p : Zero q) (a : ℚ) :
    regularArea q (rationalHit q v p a) = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    regularArea q (rationalHit q v p a) ≤ regularArea q (criticalSet q v p) :=
      NativePartialDirectionalArea.time_preimage_area_le q v (a : ℝ) _ (criticalSet_measurable q v p)
    _ = 0 := criticalSet_null q v hv p

def badSet (q : Differential X) (v : Plane) : Set (Regular q) :=
  ⋃ p : Zero q, ⋃ a : ℚ, rationalHit q v p a

theorem mem_badSet_iff (q : Differential X) (v : Plane) (x : Regular q) :
    x ∈ badSet q v ↔ ∃ p : Zero q, ∃ a : ℚ,
      (a : ℝ) ∈ domain q v x ∧ trajectory q v x (a : ℝ) ∈ criticalSet q v p := by
  simp only [badSet, mem_iUnion, mem_rationalHit_iff]

theorem badSet_measurable (q : Differential X) (v : Plane) : MeasurableSet (badSet q v) := by
  let : Countable (Zero q) := zeros_countable q
  exact MeasurableSet.iUnion (fun p => MeasurableSet.iUnion (fun a => rationalHit_measurable q v p a))

/-- Actual finite-zero/countable-time union nullness. No chosen data,
nullness, countability or partial-preservation certificate is supplied. -/
theorem badSet_null (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    regularArea q (badSet q v) = 0 := by
  let : Countable (Zero q) := zeros_countable q
  exact measure_iUnion_null (fun p => measure_iUnion_null (fun a => rationalHit_null q v hv p a))

theorem mem_badSet_of_critical_hit (q : Differential X) (v : Plane) (p : Zero q) (a : ℚ) (x : Regular q)
    (ha : (a : ℝ) ∈ domain q v x) (hcrit : trajectory q v x (a : ℝ) ∈ criticalSet q v p) :
    x ∈ badSet q v := (mem_badSet_iff q v x).mpr ⟨p, a, ha, hcrit⟩

theorem mem_badSet_of_linePreimage_hit (q : Differential X) (v : Plane) (p : Zero q) (a : ℚ) (x : Regular q)
    (ha : (a : ℝ) ∈ domain q v x)
    (hline : trajectory q v x (a : ℝ) ∈ linePreimage q (datum q p).U (datum q p).F 0 v) :
    x ∈ badSet q v :=
  mem_badSet_of_critical_hit q v p a x ha (criticalLine_subset_criticalSet q v p hline)

theorem ae_not_mem_badSet (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    ∀ᵐ x ∂regularArea q, x ∉ badSet q v := by
  exact ae_iff.mpr (by simpa only [not_not] using! badSet_null q v hv)

/-- Almost every point avoids ALL fixed critical hulls at ALL valid rational
times. This is not an assertion of AE completeness; that assembly is separate. -/
theorem ae_no_rational_critical_hit (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    ∀ᵐ x ∂regularArea q, ∀ p : Zero q, ∀ a : ℚ, (a : ℝ) ∈ domain q v x →
      trajectory q v x (a : ℝ) ∉ criticalSet q v p := by
  filter_upwards [ae_not_mem_badSet q v hv] with x hx p a ha hhit
  exact hx (mem_badSet_of_critical_hit q v p a x ha hhit)

end MNEC.NativeCriticalRays

