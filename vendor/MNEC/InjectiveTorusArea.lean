module

public import MNEC.OffSlitChartArea

@[expose] public section

/-!
# Exact area for injective physical-plane projections to arbitrary lattice tori

The plane is partitioned into translated half-open lattice cells. Each cell
has a constructed measurable inverse to the torus projection. This proves
image measurability and the area bound for all Borel sets, and exact area
preservation whenever the projection is injective on the set.

The explicit representative and cell-partition arguments adapt the user's
earlier `CriticalMeasure/TorusProjectionMeasure.lean` to arbitrary independent
lattice frames. No CriticalMeasure module is imported.
-/

noncomputable section

namespace MNEC.InjectiveTorusArea

open LatticeTorus OffSlitChartArea MeasureTheory Set
open scoped ENNReal Classical

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def cell (L : Lattice) (z : ℤ × ℤ) : Set Plane :=
  OffSlitChartArea.physicalCell L ((z.1 : ℝ), (z.2 : ℝ))

theorem mem_cell_iff (L : Lattice) (z : ℤ × ℤ) (p : Plane) :
    p ∈ cell L z ↔ L.frame.symm p ∈ coordinateCell ((z.1 : ℝ), (z.2 : ℝ)) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  · intro hp
    exact ⟨L.frame.symm p, hp, L.frame.apply_symm_apply p⟩

theorem measurableSet_cell (L : Lattice) (z : ℤ × ℤ) : MeasurableSet (cell L z) := by
  change MeasurableSet (L.frame '' coordinateCell ((z.1 : ℝ), (z.2 : ℝ)))
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  exact (measurableSet_Ioc.prod measurableSet_Ioc).preimage L.frame.symm.continuous.measurable

theorem exists_mem_cell (L : Lattice) (p : Plane) : ∃ z : ℤ × ℤ, p ∈ cell L z := by
  let q := L.frame.symm p
  refine ⟨(⌈q.1⌉ - 1, ⌈q.2⌉ - 1), ?_⟩
  apply (mem_cell_iff L _ p).mpr
  change (((⌈q.1⌉ - 1 : ℤ) : ℝ) < q.1 ∧ q.1 ≤ ((⌈q.1⌉ - 1 : ℤ) : ℝ) + 1) ∧
    (((⌈q.2⌉ - 1 : ℤ) : ℝ) < q.2 ∧ q.2 ≤ ((⌈q.2⌉ - 1 : ℤ) : ℝ) + 1)
  push_cast
  constructor
  · constructor
    · linarith only [Int.ceil_lt_add_one q.1]
    · linarith only [Int.le_ceil q.1]
  · constructor
    · linarith only [Int.ceil_lt_add_one q.2]
    · linarith only [Int.le_ceil q.2]

theorem cell_disjoint (L : Lattice) (z u : ℤ × ℤ) (hne : z ≠ u) :
    Disjoint (cell L z) (cell L u) := by
  apply Set.disjoint_left.mpr
  intro p hpz hpu
  have hz := (mem_cell_iff L z p).mp hpz
  have hu := (mem_cell_iff L u p).mp hpu
  have hcoord (x : ℝ) (m n : ℤ)
      (hm : (m : ℝ) < x ∧ x ≤ (m : ℝ) + 1)
      (hn : (n : ℝ) < x ∧ x ≤ (n : ℝ) + 1) : m = n := by
    have h₁ : (m : ℝ) < (n : ℝ) + 1 := hm.1.trans_le hn.2
    have h₂ : (n : ℝ) < (m : ℝ) + 1 := hn.1.trans_le hm.2
    have hi₁ : m < n + 1 := by exact_mod_cast h₁
    have hi₂ : n < m + 1 := by exact_mod_cast h₂
    omega
  exact hne (Prod.ext (hcoord _ _ _ hz.1 hu.1) (hcoord _ _ _ hz.2 hu.2))

def representative (L : Lattice) (z : ℤ × ℤ) (p : Torus) : Plane :=
  L.frame ((AddCircle.equivIoc (1 : ℝ) (z.1 : ℝ) p.1 : ℝ),
    (AddCircle.equivIoc (1 : ℝ) (z.2 : ℝ) p.2 : ℝ))

theorem measurable_representative (L : Lattice) (z : ℤ × ℤ) :
    Measurable (representative L z) :=
  L.frame.continuous.measurable.comp
    ((measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc (1 : ℝ) (z.1 : ℝ)).measurable.comp measurable_fst)).prodMk
      (measurable_subtype_coe.comp
        ((AddCircle.measurableEquivIoc (1 : ℝ) (z.2 : ℝ)).measurable.comp measurable_snd)))

theorem representative_mem_cell (L : Lattice) (z : ℤ × ℤ) (p : Torus) :
    representative L z p ∈ cell L z :=
  ⟨_, ⟨(AddCircle.equivIoc (1 : ℝ) (z.1 : ℝ) p.1).property,
    (AddCircle.equivIoc (1 : ℝ) (z.2 : ℝ) p.2).property⟩, rfl⟩

theorem project_representative (L : Lattice) (z : ℤ × ℤ) (p : Torus) :
    L.project (representative L z p) = p := by
  apply Prod.ext <;> simp only [Lattice.project, representative,
    ContinuousLinearEquiv.symm_apply_apply]
  · exact AddCircle.coe_equivIoc
  · exact AddCircle.coe_equivIoc

theorem representative_project (L : Lattice) (z : ℤ × ℤ) (p : Plane)
    (hp : p ∈ cell L z) : representative L z (L.project p) = p := by
  have hpc := (mem_cell_iff L z p).mp hp
  apply L.frame.symm.injective
  apply Prod.ext <;> simp only [representative, ContinuousLinearEquiv.symm_apply_apply,
    Lattice.project]
  · exact AddCircle.equivIoc_coe_of_mem hpc.1
  · exact AddCircle.equivIoc_coe_of_mem hpc.2

theorem project_image_cell (L : Lattice) (V : Set Plane) (z : ℤ × ℤ) :
    L.project '' (V ∩ cell L z) = representative L z ⁻¹' V := by
  ext p
  constructor
  · rintro ⟨x, ⟨hxV, hxcell⟩, rfl⟩
    change representative L z (L.project x) ∈ V
    rw [representative_project L z x hxcell]
    exact hxV
  · intro hp
    exact ⟨representative L z p, ⟨hp, representative_mem_cell L z p⟩,
      project_representative L z p⟩

theorem measurableSet_project_image_cell (L : Lattice) (V : Set Plane)
    (hV : MeasurableSet V) (z : ℤ × ℤ) : MeasurableSet (L.project '' (V ∩ cell L z)) := by
  rw [project_image_cell]
  exact (measurable_representative L z) hV

theorem project_preimage_image_cell (L : Lattice) (V : Set Plane) (z : ℤ × ℤ) :
    L.project ⁻¹' (L.project '' (V ∩ cell L z)) ∩ cell L z = V ∩ cell L z := by
  rw [project_image_cell]
  ext p
  constructor
  · rintro ⟨hpV, hpcell⟩
    exact ⟨by simpa only [Set.mem_preimage, representative_project L z p hpcell] using hpV,
      hpcell⟩
  · rintro ⟨hpV, hpcell⟩
    exact ⟨by simpa only [Set.mem_preimage, representative_project L z p hpcell] using hpV,
      hpcell⟩

theorem area_project_image_cell (L : Lattice) (V : Set Plane) (hV : MeasurableSet V)
    (z : ℤ × ℤ) : L.area (L.project '' (V ∩ cell L z)) = volume (V ∩ cell L z) := by
  have hm := physical_projection_area L ((z.1 : ℝ), (z.2 : ℝ))
    (L.project '' (V ∩ cell L z)) (measurableSet_project_image_cell L V hV z)
  change volume (L.project ⁻¹' (L.project '' (V ∩ cell L z)) ∩ cell L z) = _ at hm
  rw [project_preimage_image_cell] at hm
  exact hm.symm

theorem partition_by_cells (L : Lattice) (V : Set Plane) :
    V = ⋃ z : ℤ × ℤ, V ∩ cell L z := by
  ext p
  constructor
  · intro hp
    obtain ⟨z, hz⟩ := exists_mem_cell L p
    exact Set.mem_iUnion.mpr ⟨z, hp, hz⟩
  · intro hp
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hp
    exact hz.1

theorem project_image_partition (L : Lattice) (V : Set Plane) :
    L.project '' V = ⋃ z : ℤ × ℤ, L.project '' (V ∩ cell L z) := by
  conv_lhs => rw [partition_by_cells L V]
  exact Set.image_iUnion

theorem measurableSet_project_image (L : Lattice) (V : Set Plane) (hV : MeasurableSet V) :
    MeasurableSet (L.project '' V) := by
  rw [project_image_partition]
  exact MeasurableSet.iUnion (measurableSet_project_image_cell L V hV)

theorem volume_eq_sum_cells (L : Lattice) (V : Set Plane) (hV : MeasurableSet V) :
    volume V = ∑' z : ℤ × ℤ, volume (V ∩ cell L z) := by
  have hdisjoint : Pairwise (fun z u : ℤ × ℤ => Disjoint (V ∩ cell L z) (V ∩ cell L u)) := by
    intro z u hne
    exact (cell_disjoint L z u hne).mono inter_subset_right inter_subset_right
  rw [← measure_iUnion hdisjoint (fun z => hV.inter (measurableSet_cell L z)),
    ← partition_by_cells L V]

/-- Projection to a lattice torus does not increase the area of a Borel set. -/
theorem area_project_image_le (L : Lattice) (V : Set Plane) (hV : MeasurableSet V) :
    L.area (L.project '' V) ≤ volume V := by
  rw [project_image_partition, volume_eq_sum_cells L V hV]
  calc
    L.area (⋃ z : ℤ × ℤ, L.project '' (V ∩ cell L z)) ≤
        ∑' z : ℤ × ℤ, L.area (L.project '' (V ∩ cell L z)) := measure_iUnion_le _
    _ = ∑' z : ℤ × ℤ, volume (V ∩ cell L z) := tsum_congr (area_project_image_cell L V hV)

/-- Actual exact area preservation for every measurable physical set on
which the specified arbitrary lattice projection is injective. -/
theorem area_project_image_eq_of_injOn (L : Lattice) (V : Set Plane)
    (hV : MeasurableSet V) (hinj : InjOn L.project V) :
    L.area (L.project '' V) = volume V := by
  have hdisjoint : Pairwise (fun z u : ℤ × ℤ =>
      Disjoint (L.project '' (V ∩ cell L z)) (L.project '' (V ∩ cell L u))) := by
    intro z u hne
    apply Set.disjoint_left.mpr
    rintro p ⟨x, ⟨hxV, hxcell⟩, hxp⟩ ⟨y, ⟨hyV, hycell⟩, hyp⟩
    have hxy := hinj hxV hyV (hxp.trans hyp.symm)
    subst y
    exact Set.disjoint_left.mp (cell_disjoint L z u hne) hxcell hycell
  rw [project_image_partition,
    measure_iUnion hdisjoint (measurableSet_project_image_cell L V hV)]
  rw [volume_eq_sum_cells L V hV]
  exact tsum_congr (area_project_image_cell L V hV)

end MNEC.InjectiveTorusArea
