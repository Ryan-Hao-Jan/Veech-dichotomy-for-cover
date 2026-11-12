module

public import VeechDichotomy.NativeFlowboxNeighborhoods
public import Jacobians.MappingDegree.PathConnectedComplFinite
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen

/-! The actual regular locus of a native differential is path connected.
Any two regular points can therefore be connected by finitely many steps
inside concrete buffered primitive boxes. Local equality on these boxes
propagates to the entire actual regular locus. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRegularBoxChains

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeBufferedFlowboxes NativeFlowboxNeighborhoods Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem regular_pathConnected : IsPathConnected (regularSet q) :=
  Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
    (zeroSet_finite q) (regularSet_nonempty q)

def Together (x y : Regular q) : Prop := ∃ D : Data q, x ∈ D.region ∧ y ∈ D.region

theorem connected_by_boxes (x y : Regular q) : Relation.ReflTransGen (Together q) x y := by
  let : PreconnectedSpace (Regular q) :=
    isPreconnected_iff_preconnectedSpace.mp (regular_pathConnected q).isConnected.isPreconnected
  let S : Set (Regular q) := {z | Relation.ReflTransGen (Together q) x z}
  have hopen : IsOpen S := by
    apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    obtain ⟨D, hzD, _⟩ := exists_box q z isOpen_univ (mem_univ z)
    refine ⟨D.region, ?_, D.region_open, hzD⟩
    intro w hw
    exact Relation.ReflTransGen.tail hz ⟨D, hzD, hw⟩
  have hcomp : IsOpen Sᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    obtain ⟨D, hzD, _⟩ := exists_box q z isOpen_univ (mem_univ z)
    refine ⟨D.region, ?_, D.region_open, hzD⟩
    intro w hw hws
    exact hz (Relation.ReflTransGen.tail hws ⟨D, hw, hzD⟩)
  have hclosed : IsClosed S := isOpen_compl_iff.mp hcomp
  have hclopen : IsClopen S := ⟨hclosed, hopen⟩
  have huniv : S = univ := hclopen.eq_univ ⟨x, Relation.ReflTransGen.refl⟩
  have hymem : y ∈ S := huniv.symm ▸ mem_univ y
  exact hymem

theorem constant_of_box_equality {V : Type*} (f : Regular q → V)
    (hf : ∀ (D : Data q) (x : Regular q), x ∈ D.region → ∀ y ∈ D.region, f x = f y)
    (x y : Regular q) : f x = f y := by
  have hpath := connected_by_boxes q x y
  induction hpath with
  | refl => rfl
  | @tail y z _ hyz ih =>
    obtain ⟨D, hy, hz⟩ := hyz
    exact ih.trans (hf D y hy z hz)

end VeechDichotomy.NativeRegularBoxChains
