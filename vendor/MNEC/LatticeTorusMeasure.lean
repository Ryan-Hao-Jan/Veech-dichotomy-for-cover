module

public import MNEC.LatticeTorus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Haar area and null slits on arbitrary lattice tori

The canonical coordinate torus has the product of its two unit-circle Haar
measures. The physical area is this Haar probability measure multiplied by
the absolute determinant of the lattice frame. The determinant is positive
in absolute value, since the frame is an actual linear equivalence.

The null-slit proof uses actual quotient coordinates: the inverse image of
the slit lies in countably many affine lines. Fubini proves each line null,
and the unit-square quotient map is proved measure preserving. No slit
nullness or geometric area correspondence is assumed.
-/

noncomputable section

namespace MNEC.LatticeTorus

open MeasureTheory Set Topology
open scoped ENNReal Classical

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance plane_volume_addHaar : (volume : Measure Plane).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

local instance unitCircle_volume_nullSingleton :
    NullSingletonClass (volume : Measure UnitAddCircle) := by
  constructor
  intro x
  have hmp := AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := 0)
  have hpre := hmp.measure_preimage
    (measurableSet_singleton (AddCircle.equivIoc 1 0 x)).nullMeasurableSet
  have heq : (AddCircle.equivIoc 1 0) ⁻¹' {AddCircle.equivIoc 1 0 x} = {x} := by
    ext y
    simp
  rw [heq] at hpre
  rw [hpre, comap_subtype_coe_apply measurableSet_Ioc]
  simp

def canonicalArea : Measure Torus := (volume : Measure UnitAddCircle).prod volume

instance canonicalArea_probability : IsProbabilityMeasure canonicalArea where
  measure_univ := by
    rw [canonicalArea, ← univ_prod_univ, Measure.prod_prod]
    simp [AddCircle.measure_univ]

def standardProjection (p : Plane) : Torus := (p.1, p.2)

theorem continuous_standardProjection : Continuous standardProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

def unitCell : Set Plane := Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1

theorem measurePreserving_standardProjection :
    MeasurePreserving standardProjection (volume.restrict unitCell) canonicalArea := by
  have hm := (AddCircle.measurePreserving_mk (1 : ℝ) 0).prod
    (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  rw [Measure.prod_restrict] at hm
  convert hm using 1 <;> first | rfl | simp [unitCell, Measure.volume_eq_prod]

def affineLine (a v : Plane) : Set Plane :=
  {p | (p.1 - a.1) * v.2 - (p.2 - a.2) * v.1 = 0}

/-- A genuine affine line is null for planar Lebesgue measure. The proof
is adapted from the generic Fubini calculation in the user's earlier
`CriticalMeasure/TriangleInteriorParity.lean`, without importing it. -/
theorem affineLine_volume_zero (a v : Plane) (hv : v ≠ 0) :
    volume (affineLine a v) = 0 := by
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by
      intro hy
      exact hv (Prod.ext hx hy)
    have hset : affineLine a v = ({a.1} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext p
      simp [affineLine, hx, hy, sub_eq_zero]
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  · have hfiber (x : ℝ) :
        Prod.mk x ⁻¹' affineLine a v = {a.2 + (x - a.1) * v.2 / v.1} := by
      ext y
      change (x - a.1) * v.2 - (y - a.2) * v.1 = 0 ↔
        y = a.2 + (x - a.1) * v.2 / v.1
      constructor
      · intro h
        field_simp
        nlinarith only [h]
      · intro hy
        rw [hy]
        field_simp
        ring
    have hcontinuous : Continuous (fun p : Plane =>
        (p.1 - a.1) * v.2 - (p.2 - a.2) * v.1) := by fun_prop
    have hmeas : MeasurableSet (affineLine a v) :=
      measurableSet_eq_fun hcontinuous.measurable measurable_const
    rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
    simp only [hfiber, measure_singleton, lintegral_zero]

theorem Lattice.standard_preimage_slit_subset (L : Lattice) (w : Plane) :
    standardProjection ⁻¹' L.slitSet w ⊆
      ⋃ z : ℤ × ℤ, affineLine ((z.1 : ℝ), (z.2 : ℝ)) (L.frame.symm w) := by
  rintro p ⟨t, ht⟩
  let v := L.frame.symm w
  have hproj : standardProjection p = standardProjection ((t : ℝ) • v) := by
    simpa only [standardProjection, Lattice.arc, Lattice.project, map_smul] using ht.symm
  have hx : (((p.1 - (t : ℝ) * v.1 : ℝ)) : UnitAddCircle) = 0 := by
    change (p.1 : UnitAddCircle) - (((t : ℝ) * v.1 : ℝ) : UnitAddCircle) = 0
    exact sub_eq_zero.mpr (congrArg Prod.fst hproj)
  have hy : (((p.2 - (t : ℝ) * v.2 : ℝ)) : UnitAddCircle) = 0 := by
    change (p.2 : UnitAddCircle) - (((t : ℝ) * v.2 : ℝ) : UnitAddCircle) = 0
    exact sub_eq_zero.mpr (congrArg Prod.snd hproj)
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hy
  have hm' : p.1 - (m : ℝ) = (t : ℝ) * v.1 := by
    have hm'' : (m : ℝ) = p.1 - (t : ℝ) * v.1 := by simpa using hm
    linarith
  have hn' : p.2 - (n : ℝ) = (t : ℝ) * v.2 := by
    have hn'' : (n : ℝ) = p.2 - (t : ℝ) * v.2 := by simpa using hn
    linarith
  apply Set.mem_iUnion.mpr
  refine ⟨(m, n), ?_⟩
  change (p.1 - (m : ℝ)) * v.2 - (p.2 - (n : ℝ)) * v.1 = 0
  rw [hm', hn']
  ring

theorem Lattice.canonicalArea_slitSet_zero (L : Lattice) (w : Plane) :
    canonicalArea (L.slitSet w) = 0 := by
  by_cases hw : w = 0
  · subst w
    have hset : L.slitSet 0 = {0} := by
      ext p
      constructor
      · rintro ⟨t, rfl⟩
        simp [Lattice.arc]
      · intro hp
        rw [Set.mem_singleton_iff] at hp
        refine ⟨⟨0, by norm_num⟩, ?_⟩
        simp [Lattice.arc, hp]
    rw [hset]
    simp [canonicalArea]
  · have hv : L.frame.symm w ≠ 0 := by
      intro hv
      apply hw
      simpa using congrArg L.frame hv
    have hpre : volume (standardProjection ⁻¹' L.slitSet w) = 0 :=
      measure_mono_null (L.standard_preimage_slit_subset w)
        (measure_iUnion_null fun z : ℤ × ℤ => affineLine_volume_zero _ _ hv)
    have hmeas : MeasurableSet (L.slitSet w) := (L.slitSet_closed w).measurableSet
    rw [← measurePreserving_standardProjection.measure_preimage hmeas.nullMeasurableSet,
      Measure.restrict_apply (hmeas.preimage continuous_standardProjection.measurable)]
    exact measure_mono_null Set.inter_subset_left hpre

def Lattice.covolume (L : Lattice) : ℝ :=
  |LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane)|

theorem Lattice.covolume_pos (L : Lattice) : 0 < L.covolume :=
  abs_pos.mpr (LinearEquiv.isUnit_det' L.frame.toLinearEquiv).ne_zero

def Lattice.area (L : Lattice) : Measure Torus := ENNReal.ofReal L.covolume • canonicalArea

theorem Lattice.area_univ (L : Lattice) : L.area univ = ENNReal.ofReal L.covolume := by
  simp [Lattice.area]

theorem Lattice.area_univ_pos (L : Lattice) : 0 < L.area univ := by
  rw [L.area_univ]
  exact ENNReal.ofReal_pos.mpr L.covolume_pos

theorem Lattice.area_univ_ne_top (L : Lattice) : L.area univ ≠ ∞ := by
  rw [L.area_univ]
  exact ENNReal.ofReal_ne_top

theorem Lattice.area_slitSet_zero (L : Lattice) (w : Plane) : L.area (L.slitSet w) = 0 := by
  simp [Lattice.area, L.canonicalArea_slitSet_zero w]

theorem Lattice.area_off_slit (L : Lattice) (w : Plane) :
    L.area (L.slitSet w)ᶜ = ENNReal.ofReal L.covolume := by
  have heq : (L.slitSet w)ᶜ =ᵐ[L.area] univ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (L.area_slitSet_zero w)] with p hp
    exact propext ⟨fun _ => Set.mem_univ _, fun _ => hp⟩
  rw [measure_congr heq, L.area_univ]

def Lattice.physicalCell (L : Lattice) : Set Plane := L.frame '' unitCell

/-- The fundamental half-open parallelogram has actual planar Lebesgue
area equal to the absolute determinant of the lattice frame. -/
theorem Lattice.physicalCell_volume (L : Lattice) :
    volume L.physicalCell = ENNReal.ofReal L.covolume := by
  rw [Lattice.physicalCell,
    (volume : Measure Plane).addHaar_image_continuousLinearEquiv L.frame]
  have hcell : volume unitCell = 1 := by
    simp [unitCell, Measure.volume_eq_prod, Measure.prod_prod]
  rw [hcell, mul_one]
  rfl

theorem Lattice.project_preimage_inter_physicalCell (L : Lattice) (U : Set Torus) :
    L.project ⁻¹' U ∩ L.physicalCell =
      L.frame '' (standardProjection ⁻¹' U ∩ unitCell) := by
  ext p
  constructor
  · rintro ⟨hp, x, hx, rfl⟩
    refine ⟨x, ⟨?_, hx⟩, rfl⟩
    simpa only [Set.mem_preimage, Lattice.project, standardProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hp
  · rintro ⟨x, ⟨hx, hcell⟩, rfl⟩
    refine ⟨?_, x, hcell, rfl⟩
    simpa only [Set.mem_preimage, Lattice.project, standardProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hx

/-- Actual planar area in a fundamental parallelogram induces precisely
the determinant-scaled Haar area, rather than assuming that identification. -/
theorem Lattice.physical_projection_area (L : Lattice) (U : Set Torus)
    (hU : MeasurableSet U) :
    volume (L.project ⁻¹' U ∩ L.physicalCell) = L.area U := by
  rw [L.project_preimage_inter_physicalCell,
    (volume : Measure Plane).addHaar_image_continuousLinearEquiv L.frame]
  have hstandard := measurePreserving_standardProjection.measure_preimage
    hU.nullMeasurableSet
  rw [Measure.restrict_apply (hU.preimage continuous_standardProjection.measurable)]
    at hstandard
  rw [hstandard]
  rfl

theorem Lattice.measurePreserving_project_physicalCell (L : Lattice) :
    MeasurePreserving L.project (volume.restrict L.physicalCell) L.area where
  measurable := L.continuous_project.measurable
  map_eq := by
    apply Measure.ext
    intro U hU
    rw [Measure.map_apply L.continuous_project.measurable hU,
      Measure.restrict_apply (hU.preimage L.continuous_project.measurable)]
    exact L.physical_projection_area U hU

end MNEC.LatticeTorus

