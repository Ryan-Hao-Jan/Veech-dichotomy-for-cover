module

public import MNEC.NativeLocalPrimitives
public import MNEC.NativeRegularArea
public import MNEC.LatticeTorusMeasure

@[expose] public section
noncomputable section

namespace MNEC.NativePrimitiveLineNull

open LatticeTorus NativeAbelianDifferential NativePrimitiveTransitions
open NativeRegularTranslationAtlas NativeRegularArea NativeLocalPrimitives
open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def linePreimage (q : Differential X) (U : Set X) (F : X → ℂ) (a v : Plane) : Set (Regular q) :=
  {x | x.val ∈ U ∧ toPlane (F x.val) ∈ affineLine a v}

theorem affineLine_measurable (a v : Plane) : MeasurableSet (affineLine a v) := by
  have hc : Continuous (fun p : Plane => (p.1 - a.1) * v.2 - (p.2 - a.2) * v.1) := by fun_prop
  exact measurableSet_eq_fun hc.measurable measurable_const

theorem mem_affineLine_sub (p a c v : Plane) (hp : p ∈ affineLine a v) :
    p - c ∈ affineLine (a - c) v := by
  change (p.1 - a.1) * v.2 - (p.2 - a.2) * v.1 = 0 at hp
  change (p.1 - c.1 - (a.1 - c.1)) * v.2 - (p.2 - c.2 - (a.2 - c.2)) * v.1 = 0
  nlinarith only [hp]

/-- A primitive function differs by a constant from a genuine primitive
chart near each regular point. This derives local area nullness directly
from the actual chart Lebesgue formula, without injectivity of F. -/
theorem exists_null_line_patch (q : Differential X) (U : Set X) (hU : IsOpen U)
    (F : X → ℂ) (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (a v : Plane) (hv : v ≠ 0) (x : Regular q) (hxU : x.val ∈ U) :
    ∃ W : Set (Regular q), IsOpen W ∧ x ∈ W ∧ regularArea q (linePreimage q U F a v ∩ W) = 0 := by
  let e := primitiveChart q x
  let E := coordinateChart q x
  let c := F x.val - e x.val
  have hdiff : ∀ᶠ y in 𝓝 x.val, F y = e y + c :=
    NativeLocalPrimitives.difference_germ q e F e.source U e.open_source hU
      (chosen q x).derivative hF x.val ⟨(chosen q x).center, hxU⟩
  have hsubdiff : ∀ᶠ y : Regular q in 𝓝 x, F y.val = e y.val + c :=
    continuous_subtype_val.continuousAt hdiff
  have hxV : x ∈ (Subtype.val : Regular q → X) ⁻¹' U := hxU
  have hnear : ∀ᶠ y : Regular q in 𝓝 x,
      y ∈ E.source ∧ y.val ∈ U ∧ F y.val = e y.val + c := by
    filter_upwards [E.open_source.mem_nhds (coordinateChart_center q x),
      (hU.preimage continuous_subtype_val).mem_nhds hxV, hsubdiff] with y hyE hyU hyF
    exact ⟨hyE, hyU, hyF⟩
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hnear
  let B := affineLine (a - toPlane c) v ∩ E.target
  have hB : MeasurableSet B := (affineLine_measurable _ _).inter E.open_target.measurableSet
  have hvol : volume B = 0 := measure_mono_null inter_subset_left (affineLine_volume_zero _ _ hv)
  have harea : regularArea q (E.symm '' B) = 0 :=
    (coordinateChart_image q x B hB inter_subset_right).trans hvol
  refine ⟨W, hW, hxW, measure_mono_null ?_ harea⟩
  rintro y ⟨hyA, hyW⟩
  have hy := hWsub hyW
  have hphys : E y = toPlane (F y.val) - toPlane c := by
    rw [coordinateChart_apply]
    have hmap := congrArg toPlane hy.2.2
    rw [map_add] at hmap
    change toPlane (e y.val) = _
    rw [hmap]
    abel
  exact ⟨E y, ⟨by rw [hphys]; exact mem_affineLine_sub _ _ _ _ hyA.2, E.map_source hy.1⟩,
    E.left_inv hy.1⟩

/-- On the actual regular phase, the preimage of ANY genuine physical affine
line under an actual primitive function has canonical area zero. A derived
SCT countable subcover replaces any global injectivity/normal-form premise. -/
theorem linePreimage_null (q : Differential X) (U : Set X) (hU : IsOpen U)
    (F : X → ℂ) (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (a v : Plane) (hv : v ≠ 0) : regularArea q (linePreimage q U F a v) = 0 := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  let V : Set (Regular q) := Subtype.val ⁻¹' U
  by_cases hV : V.Nonempty
  · let T := ↥V
    let : Nonempty T := hV.to_subtype
    have hp : ∀ x : T, ∃ W : Set (Regular q), IsOpen W ∧ x.val ∈ W ∧
        regularArea q (linePreimage q U F a v ∩ W) = 0 :=
      fun x => exists_null_line_patch q U hU F hF a v hv x.val x.property
    choose W hW hxW hnull using hp
    have hcover : V ⊆ ⋃ x : T, W x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof V).indexed_countable_subcover W hW hcover
    have hsub : linePreimage q U F a v ⊆ ⋃ n : ℕ, linePreimage q U F a v ∩ W (f n) := by
      intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hx.1)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
    exact measure_mono_null hsub (measure_iUnion_null (fun n => hnull (f n)))
  · have hempty : linePreimage q U F a v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hV ⟨x, hx.1⟩
    rw [hempty, measure_empty]

/-- At every original point, including a zero, construct a normalized local
primitive whose physical affine-line preimages on the regular locus are null. -/
theorem exists_local_primitive_with_null_lines (q : Differential X) (b : X) :
    ∃ U : Set X, IsOpen U ∧ b ∈ U ∧ ∃ F : X → ℂ, F b = 0 ∧
      (∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y)) ∧ ContinuousOn F U ∧
      ∀ a v : Plane, v ≠ 0 → regularArea q (linePreimage q U F a v) = 0 := by
  obtain ⟨U, hU, hb, F, hbF, hF, hcont⟩ := exists_local_primitive_function q b
  exact ⟨U, hU, hb, F, hbF, hF, hcont, fun a v hv => linePreimage_null q U hU F hF a v hv⟩

end MNEC.NativePrimitiveLineNull

