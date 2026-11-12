module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Tori for arbitrary real plane lattices

A lattice is given by a real basis, represented by a continuous linear
equivalence. Its torus is the actual coordinate quotient (R/Z)^2; the
physical-plane projection has exactly the specified lattice as its kernel.
No rational relation or isogeny between different lattices is imposed.

These definitions are a starting point for general slit connected sums.
No assertion about the topology or flow of a genus-two connected sum is
made in this file.
-/

noncomputable section

namespace MNEC.LatticeTorus

open Set Topology

abbrev Plane := ℝ × ℝ
abbrev Torus := UnitAddCircle × UnitAddCircle
abbrev Parameter := Icc (0 : ℝ) 1

structure Lattice where
  frame : Plane ≃L[ℝ] Plane

def Lattice.period (L : Lattice) (z : ℤ × ℤ) : Plane :=
  L.frame ((z.1 : ℝ), (z.2 : ℝ))

def Lattice.project (L : Lattice) (x : Plane) : Torus :=
  ((L.frame.symm x).1, (L.frame.symm x).2)

theorem Lattice.continuous_project (L : Lattice) : Continuous L.project :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_fst.comp L.frame.symm.continuous)).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_snd.comp L.frame.symm.continuous))

@[simp] theorem Lattice.project_zero (L : Lattice) : L.project 0 = 0 := by
  simp [Lattice.project]

@[simp] theorem Lattice.project_add (L : Lattice) (x y : Plane) :
    L.project (x + y) = L.project x + L.project y := by
  simp [Lattice.project, map_add]

@[simp] theorem Lattice.project_neg (L : Lattice) (x : Plane) :
    L.project (-x) = -L.project x := by
  simp [Lattice.project, map_neg]

@[simp] theorem Lattice.project_sub (L : Lattice) (x y : Plane) :
    L.project (x - y) = L.project x - L.project y := by
  simp [sub_eq_add_neg]

theorem Lattice.project_eq_zero_iff (L : Lattice) (x : Plane) :
    L.project x = 0 ↔ ∃ z : ℤ × ℤ, x = L.period z := by
  constructor
  · intro hx
    have hx₁ : (((L.frame.symm x).1 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.fst hx
    have hx₂ : (((L.frame.symm x).2 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.snd hx
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx₁
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx₂
    have hm' : (L.frame.symm x).1 = (m : ℝ) := by simpa using hm.symm
    have hn' : (L.frame.symm x).2 = (n : ℝ) := by simpa using hn.symm
    refine ⟨(m, n), ?_⟩
    apply L.frame.symm.injective
    simpa only [Lattice.period, ContinuousLinearEquiv.symm_apply_apply] using
      Prod.ext hm' hn'
  · rintro ⟨z, rfl⟩
    simp only [Lattice.project, Lattice.period, ContinuousLinearEquiv.symm_apply_apply]
    apply Prod.ext
    · apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨z.1, by simp⟩
    · apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨z.2, by simp⟩

theorem Lattice.project_eq_iff (L : Lattice) (x y : Plane) :
    L.project x = L.project y ↔ ∃ z : ℤ × ℤ, x - y = L.period z := by
  rw [← L.project_eq_zero_iff (x - y), L.project_sub, sub_eq_zero]

theorem Lattice.period_injective (L : Lattice) : Function.Injective L.period := by
  intro z w h
  have h' := L.frame.injective h
  apply Prod.ext
  · have hx : (z.1 : ℝ) = (w.1 : ℝ) := congrArg Prod.fst h'
    exact_mod_cast hx
  · have hy : (z.2 : ℝ) = (w.2 : ℝ) := congrArg Prod.snd h'
    exact_mod_cast hy

theorem Lattice.project_surjective (L : Lattice) : Function.Surjective L.project := by
  intro p
  obtain ⟨x, hx⟩ := Quotient.exists_rep p.1
  obtain ⟨y, hy⟩ := Quotient.exists_rep p.2
  refine ⟨L.frame (x, y), ?_⟩
  simpa only [Lattice.project, ContinuousLinearEquiv.symm_apply_apply] using Prod.ext hx hy

theorem Lattice.isOpenMap_project (L : Lattice) : IsOpenMap L.project := by
  exact (QuotientAddGroup.isOpenMap_coe.prodMap QuotientAddGroup.isOpenMap_coe).comp
    L.frame.symm.toHomeomorph.isOpenMap

def Lattice.arc (L : Lattice) (w : Plane) (t : Parameter) : Torus :=
  L.project ((t : ℝ) • w)

def Lattice.EmbeddedSlit (L : Lattice) (w : Plane) : Prop := Function.Injective (L.arc w)

def Lattice.slitSet (L : Lattice) (w : Plane) : Set Torus := range (L.arc w)

theorem Lattice.continuous_arc (L : Lattice) (w : Plane) : Continuous (L.arc w) :=
  L.continuous_project.comp (continuous_subtype_val.smul continuous_const)

theorem Lattice.slitSet_compact (L : Lattice) (w : Plane) : IsCompact (L.slitSet w) :=
  isCompact_range (L.continuous_arc w)

theorem Lattice.slitSet_closed (L : Lattice) (w : Plane) : IsClosed (L.slitSet w) :=
  (L.slitSet_compact w).isClosed

theorem Lattice.arc_closedEmbedding (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w) :
    IsClosedEmbedding (L.arc w) := (L.continuous_arc w).isClosedEmbedding hw

theorem Lattice.embeddedSlit_iff (L : Lattice) (w : Plane) :
    L.EmbeddedSlit w ↔
      ∀ s t : Parameter, (∃ z : ℤ × ℤ, ((s : ℝ) - (t : ℝ)) • w = L.period z) → s = t := by
  constructor
  · intro h s t hperiod
    apply h
    apply (L.project_eq_iff _ _).mpr
    simpa only [← sub_smul] using hperiod
  · intro h s t heq
    apply h s t
    have hp := (L.project_eq_iff _ _).mp heq
    simpa only [← sub_smul] using hp

private theorem int_eq_zero_of_cast_abs_lt_one (m : ℤ) (hm : |(m : ℝ)| < 1) : m = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hm
  have hlo' : (-1 : ℤ) < m := by exact_mod_cast hlo
  have hhi' : m < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- Smallness is checked in actual lattice coordinates and proves that the
projected segment is embedded; embeddedness is not supplied as a premise. -/
theorem Lattice.embedded_of_coordinate_small (L : Lattice) (w : Plane)
    (hw : w ≠ 0) (h₁ : |(L.frame.symm w).1| < 1)
    (h₂ : |(L.frame.symm w).2| < 1) : L.EmbeddedSlit w := by
  apply (L.embeddedSlit_iff w).mpr
  intro s t hp
  obtain ⟨z, hz⟩ := hp
  have hst : |(s : ℝ) - (t : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
  have hz' : ((s : ℝ) - (t : ℝ)) • L.frame.symm w = ((z.1 : ℝ), (z.2 : ℝ)) := by
    simpa only [map_smul, Lattice.period, ContinuousLinearEquiv.symm_apply_apply] using
      congrArg L.frame.symm hz
  have hzm : z.1 = 0 := by
    apply int_eq_zero_of_cast_abs_lt_one
    have hcoord : ((s : ℝ) - (t : ℝ)) * (L.frame.symm w).1 = (z.1 : ℝ) :=
      congrArg Prod.fst hz'
    rw [← hcoord, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hst).trans_lt h₁
  have hzn : z.2 = 0 := by
    apply int_eq_zero_of_cast_abs_lt_one
    have hcoord : ((s : ℝ) - (t : ℝ)) * (L.frame.symm w).2 = (z.2 : ℝ) :=
      congrArg Prod.snd hz'
    rw [← hcoord, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hst).trans_lt h₂
  have hzero : ((s : ℝ) - (t : ℝ)) • w = 0 := by
    simpa only [Lattice.period, hzm, hzn, Int.cast_zero, ← Prod.zero_eq_mk, map_zero] using hz
  have hscalar : (s : ℝ) - (t : ℝ) = 0 := (smul_eq_zero.mp hzero).resolve_right hw
  exact Subtype.ext (sub_eq_zero.mp hscalar)

/-- Any two real plane lattices admit a common nonzero embedded slit.
The witness is explicitly scaled in the physical horizontal direction. -/
theorem common_embedded_slit_exists (L₁ L₂ : Lattice) :
    ∃ w : Plane, w ≠ 0 ∧ L₁.EmbeddedSlit w ∧ L₂.EmbeddedSlit w := by
  let u : Plane := (1, 0)
  let v₁ := L₁.frame.symm u
  let v₂ := L₂.frame.symm u
  let M := 1 + |v₁.1| + |v₁.2| + |v₂.1| + |v₂.2|
  have hM : 0 < M := by
    dsimp [M]
    linarith [abs_nonneg v₁.1, abs_nonneg v₁.2, abs_nonneg v₂.1, abs_nonneg v₂.2]
  let r := 1 / M
  have hr : 0 < r := one_div_pos.mpr hM
  have hcoord (x : ℝ) (hx : |x| < M) : |r * x| < 1 := by
    rw [abs_mul, abs_of_pos hr]
    have hquot : |x| / M < 1 := (div_lt_one hM).mpr hx
    simpa only [r, one_div, div_eq_mul_inv, mul_comm, one_mul] using hquot
  have h₁ : |v₁.1| < M := by dsimp [M]; linarith [abs_nonneg v₁.2, abs_nonneg v₂.1, abs_nonneg v₂.2]
  have h₂ : |v₁.2| < M := by dsimp [M]; linarith [abs_nonneg v₁.1, abs_nonneg v₂.1, abs_nonneg v₂.2]
  have h₃ : |v₂.1| < M := by dsimp [M]; linarith [abs_nonneg v₁.1, abs_nonneg v₁.2, abs_nonneg v₂.2]
  have h₄ : |v₂.2| < M := by dsimp [M]; linarith [abs_nonneg v₁.1, abs_nonneg v₁.2, abs_nonneg v₂.1]
  have hw : r • u ≠ (0 : Plane) := by
    intro h
    have hz : r = 0 := by simpa only [u, Prod.smul_fst, smul_eq_mul, mul_one, Prod.fst_zero] using congrArg Prod.fst h
    exact hr.ne' hz
  refine ⟨r • u, hw, L₁.embedded_of_coordinate_small _ hw ?_ ?_,
    L₂.embedded_of_coordinate_small _ hw ?_ ?_⟩
  · simpa only [map_smul, Prod.smul_fst, smul_eq_mul] using hcoord v₁.1 h₁
  · simpa only [map_smul, Prod.smul_snd, smul_eq_mul] using hcoord v₁.2 h₂
  · simpa only [map_smul, Prod.smul_fst, smul_eq_mul] using hcoord v₂.1 h₃
  · simpa only [map_smul, Prod.smul_snd, smul_eq_mul] using hcoord v₂.2 h₄

end MNEC.LatticeTorus
