module

public import MNEC.LatticeTorus
public import Mathlib.Data.Int.GCD
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Actual integral rebasing at a primitive lattice period

The second column is computed by the integer extended Euclidean algorithm.
The resulting determinant-one integer and real linear equivalences rebase
the physical lattice frame. The induced coordinate-torus homeomorphism
preserves the physical projection. No cut or glued-surface isomorphism is
assumed or asserted.
-/

noncomputable section

namespace MNEC.PrimitiveLatticeRebasing

open LatticeTorus Set Topology

def Primitive (m n : ℤ) : Prop := Int.gcd m n = 1

def partner (m n : ℤ) : ℤ × ℤ := (-Int.gcdB m n, Int.gcdA m n)

theorem determinant_one (m n : ℤ) (h : Primitive m n) :
    m * (partner m n).2 - n * (partner m n).1 = 1 := by
  have hbezout := Int.gcd_eq_gcd_ab m n
  rw [h] at hbezout
  simpa [partner] using hbezout.symm

theorem primitive_pair_ne_zero (m n : ℤ) (h : Primitive m n) :
    (m, n) ≠ (0 : ℤ × ℤ) := by
  intro hz
  have hm : m = 0 := congrArg Prod.fst hz
  have hn : n = 0 := congrArg Prod.snd hz
  have hd := determinant_one m n h
  simp [hm, hn] at hd

def integerMatrix (m n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![m, (partner m n).1; n, (partner m n).2]

theorem integerMatrix_det (m n : ℤ) (h : Primitive m n) :
    (integerMatrix m n).det = 1 := by
  rw [integerMatrix, Matrix.det_fin_two]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_comm n] using determinant_one m n h

def columnEquiv {R : Type*} [CommRing R] (m n p q : R)
    (h : m * q - n * p = 1) : (R × R) ≃ₗ[R] (R × R) where
  toFun z := (m * z.1 + p * z.2, n * z.1 + q * z.2)
  invFun z := (q * z.1 - p * z.2, -n * z.1 + m * z.2)
  left_inv z := by
    apply Prod.ext
    · change q * (m * z.1 + p * z.2) - p * (n * z.1 + q * z.2) = z.1
      calc
        _ = (m * q - n * p) * z.1 := by ring
        _ = z.1 := by rw [h, one_mul]
    · change -n * (m * z.1 + p * z.2) + m * (n * z.1 + q * z.2) = z.2
      calc
        _ = (m * q - n * p) * z.2 := by ring
        _ = z.2 := by rw [h, one_mul]
  right_inv z := by
    apply Prod.ext
    · change m * (q * z.1 - p * z.2) + p * (-n * z.1 + m * z.2) = z.1
      calc
        _ = (m * q - n * p) * z.1 := by ring
        _ = z.1 := by rw [h, one_mul]
    · change n * (q * z.1 - p * z.2) + q * (-n * z.1 + m * z.2) = z.2
      calc
        _ = (m * q - n * p) * z.2 := by ring
        _ = z.2 := by rw [h, one_mul]
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' c x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

def integerBasisChange (m n : ℤ) (h : Primitive m n) :
    (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  columnEquiv m n (partner m n).1 (partner m n).2 (determinant_one m n h)

@[simp] theorem integerBasisChange_apply (m n : ℤ) (h : Primitive m n) (z : ℤ × ℤ) :
    integerBasisChange m n h z =
      (m * z.1 + (partner m n).1 * z.2, n * z.1 + (partner m n).2 * z.2) := rfl

@[simp] theorem integerBasisChange_symm_apply (m n : ℤ) (h : Primitive m n) (z : ℤ × ℤ) :
    (integerBasisChange m n h).symm z =
      ((partner m n).2 * z.1 - (partner m n).1 * z.2, -n * z.1 + m * z.2) := rfl

def integerBasis (m n : ℤ) (h : Primitive m n) : Module.Basis (Fin 2) ℤ (ℤ × ℤ) :=
  (Module.Basis.finTwoProd ℤ).map (integerBasisChange m n h)

@[simp] theorem integerBasis_zero (m n : ℤ) (h : Primitive m n) :
    integerBasis m n h 0 = (m, n) := by
  simp [integerBasis]

@[simp] theorem integerBasis_one (m n : ℤ) (h : Primitive m n) :
    integerBasis m n h 1 = partner m n := by
  simp [integerBasis]

theorem real_determinant_one (m n : ℤ) (h : Primitive m n) :
    (m : ℝ) * ((partner m n).2 : ℝ) - (n : ℝ) * ((partner m n).1 : ℝ) = 1 := by
  exact_mod_cast determinant_one m n h

def realBasisChange (m n : ℤ) (h : Primitive m n) : Plane ≃L[ℝ] Plane :=
  (columnEquiv (m : ℝ) (n : ℝ) ((partner m n).1 : ℝ) ((partner m n).2 : ℝ)
    (real_determinant_one m n h)).toContinuousLinearEquiv

@[simp] theorem realBasisChange_apply (m n : ℤ) (h : Primitive m n) (x : Plane) :
    realBasisChange m n h x =
      ((m : ℝ) * x.1 + ((partner m n).1 : ℝ) * x.2,
        (n : ℝ) * x.1 + ((partner m n).2 : ℝ) * x.2) := rfl

@[simp] theorem realBasisChange_symm_apply (m n : ℤ) (h : Primitive m n) (x : Plane) :
    (realBasisChange m n h).symm x =
      (((partner m n).2 : ℝ) * x.1 - ((partner m n).1 : ℝ) * x.2,
        -(n : ℝ) * x.1 + (m : ℝ) * x.2) := rfl

theorem realBasisChange_integer (m n : ℤ) (h : Primitive m n) (z : ℤ × ℤ) :
    realBasisChange m n h ((z.1 : ℝ), (z.2 : ℝ)) =
      (((integerBasisChange m n h z).1 : ℝ), ((integerBasisChange m n h z).2 : ℝ)) := by
  simp only [realBasisChange_apply, integerBasisChange_apply, Int.cast_add, Int.cast_mul]

def rebased (L : Lattice) (m n : ℤ) (h : Primitive m n) : Lattice where
  frame := (realBasisChange m n h).trans L.frame

@[simp] theorem rebased_coordinates (L : Lattice) (m n : ℤ) (h : Primitive m n) (x : Plane) :
    (rebased L m n h).frame.symm x = (realBasisChange m n h).symm (L.frame.symm x) := rfl

theorem primitive_period_ne_zero (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    L.period (m, n) ≠ 0 := by
  intro hz
  apply primitive_pair_ne_zero m n h
  apply L.period_injective
  simpa [Lattice.period] using hz

theorem rebased_period (L : Lattice) (m n : ℤ) (h : Primitive m n) (z : ℤ × ℤ) :
    (rebased L m n h).period z = L.period (integerBasisChange m n h z) := by
  simp only [Lattice.period, rebased, ContinuousLinearEquiv.trans_apply,
    realBasisChange_integer]

@[simp] theorem rebased_first_period (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    (rebased L m n h).period (1, 0) = L.period (m, n) := by
  simp [rebased_period]

@[simp] theorem rebased_second_period (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    (rebased L m n h).period (0, 1) = L.period (partner m n) := by
  simp [rebased_period]

theorem rebased_period_range (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    range (rebased L m n h).period = range L.period := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨integerBasisChange m n h z, (rebased_period L m n h z).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨u, rfl⟩ := (integerBasisChange m n h).surjective z
    exact ⟨u, rebased_period L m n h u⟩

def torusQuotient (x : Plane) : Torus := ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))

private theorem torusQuotient_surjective : Function.Surjective torusQuotient := by
  rintro ⟨x, y⟩
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  obtain ⟨b, hb⟩ := Quotient.exists_rep y
  exact ⟨(a, b), Prod.ext ha hb⟩

def torusForward (m n : ℤ) (z : Torus) : Torus :=
  (m • z.1 + (partner m n).1 • z.2, n • z.1 + (partner m n).2 • z.2)

def torusBackward (m n : ℤ) (z : Torus) : Torus :=
  ((partner m n).2 • z.1 - (partner m n).1 • z.2, -n • z.1 + m • z.2)

private theorem torusForward_quotient (m n : ℤ) (h : Primitive m n) (x : Plane) :
    torusForward m n (torusQuotient x) = torusQuotient (realBasisChange m n h x) := by
  ext <;> simp only [torusForward, torusQuotient, realBasisChange_apply,
    ← AddCircle.coe_zsmul, ← AddCircle.coe_add, zsmul_eq_mul]

private theorem torusBackward_quotient (m n : ℤ) (h : Primitive m n) (x : Plane) :
    torusBackward m n (torusQuotient x) = torusQuotient ((realBasisChange m n h).symm x) := by
  ext <;> simp only [torusBackward, torusQuotient, realBasisChange_symm_apply,
    ← AddCircle.coe_zsmul, ← AddCircle.coe_add, ← AddCircle.coe_sub, zsmul_eq_mul, Int.cast_neg]

/-- The map takes new lattice coordinates to old lattice coordinates. -/
def torusHomeomorph (m n : ℤ) (h : Primitive m n) : Torus ≃ₜ Torus where
  toFun := torusForward m n
  invFun := torusBackward m n
  left_inv z := by
    obtain ⟨x, rfl⟩ := torusQuotient_surjective z
    rw [torusForward_quotient m n h, torusBackward_quotient m n h,
      ContinuousLinearEquiv.symm_apply_apply]
  right_inv z := by
    obtain ⟨x, rfl⟩ := torusQuotient_surjective z
    rw [torusBackward_quotient m n h, torusForward_quotient m n h,
      ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := by
    exact ((continuous_fst.zsmul m).add (continuous_snd.zsmul (partner m n).1)).prodMk
      ((continuous_fst.zsmul n).add (continuous_snd.zsmul (partner m n).2))
  continuous_invFun := by
    exact ((continuous_fst.zsmul (partner m n).2).sub (continuous_snd.zsmul (partner m n).1)).prodMk
      ((continuous_fst.zsmul (-n)).add (continuous_snd.zsmul m))

theorem torusHomeomorph_project (L : Lattice) (m n : ℤ) (h : Primitive m n) (x : Plane) :
    torusHomeomorph m n h ((rebased L m n h).project x) = L.project x := by
  change torusForward m n
    (torusQuotient (((realBasisChange m n h).trans L.frame).symm x)) =
      torusQuotient (L.frame.symm x)
  rw [torusForward_quotient m n h]
  congr 1
  exact (realBasisChange m n h).apply_symm_apply (L.frame.symm x)

theorem torusHomeomorph_arc (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (t : Parameter) :
    torusHomeomorph m n h ((rebased L m n h).arc w t) = L.arc w t :=
  torusHomeomorph_project L m n h ((t : ℝ) • w)

theorem torusHomeomorph_slitSet (L : Lattice) (m n : ℤ) (h : Primitive m n) (w : Plane) :
    torusHomeomorph m n h '' (rebased L m n h).slitSet w = L.slitSet w := by
  ext p
  constructor
  · rintro ⟨q, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (torusHomeomorph_arc L m n h w t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(rebased L m n h).arc w t, ⟨t, rfl⟩, torusHomeomorph_arc L m n h w t⟩

theorem rebased_embeddedSlit_iff (L : Lattice) (m n : ℤ) (h : Primitive m n) (w : Plane) :
    (rebased L m n h).EmbeddedSlit w ↔ L.EmbeddedSlit w := by
  constructor
  · intro he s t hst
    apply he
    apply (torusHomeomorph m n h).injective
    simpa only [torusHomeomorph_arc] using hst
  · intro he s t hst
    apply he
    have hst' := congrArg (torusHomeomorph m n h) hst
    simpa only [torusHomeomorph_arc] using hst'

end MNEC.PrimitiveLatticeRebasing

