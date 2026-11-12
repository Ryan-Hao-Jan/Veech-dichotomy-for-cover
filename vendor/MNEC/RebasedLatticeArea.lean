module

public import MNEC.CutLatticeRebasing
public import MNEC.TorusFlow
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-!
# Physical area under a computed primitive lattice rebasing

The real basis change has determinant one. Its coordinate-torus map is
proved additive from the physical projection law and project surjectivity.
Uniqueness of normalized Haar measure proves coordinate area preservation;
the computed covolume identity then proves physical area preservation.
-/

noncomputable section

namespace MNEC.RebasedLatticeArea

open LatticeTorus PrimitiveLatticeRebasing CutLatticeRebasing MeasureTheory Set

theorem realBasisChange_linearMap (m n : ℤ) (h : Primitive m n) :
    (realBasisChange m n h : Plane →ₗ[ℝ] Plane) =
      Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        !![(m : ℝ), ((partner m n).1 : ℝ); (n : ℝ), ((partner m n).2 : ℝ)] := by
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin_finTwoProd_apply]
  exact realBasisChange_apply m n h x

theorem realBasisChange_det (m n : ℤ) (h : Primitive m n) :
    LinearMap.det (realBasisChange m n h : Plane →ₗ[ℝ] Plane) = 1 := by
  rw [realBasisChange_linearMap, LinearMap.det_toLin, Matrix.det_fin_two]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_comm (n : ℝ)] using real_determinant_one m n h

theorem rebased_covolume (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    (rebased L m n h).covolume = L.covolume := by
  unfold Lattice.covolume
  change |LinearMap.det ((L.frame : Plane →ₗ[ℝ] Plane).comp
    (realBasisChange m n h : Plane →ₗ[ℝ] Plane))| = _
  rw [LinearMap.det_comp, realBasisChange_det, mul_one]

end MNEC.RebasedLatticeArea

namespace MNEC.CutLatticeRebasing.PhysicalTorusEquiv

open LatticeTorus MeasureTheory Set

variable {L M : Lattice}

theorem torus_map_zero (e : PhysicalTorusEquiv L M) : e.torus 0 = 0 := by
  simpa only [Lattice.project_zero] using e.project_eq 0

theorem torus_map_add (e : PhysicalTorusEquiv L M) (p q : Torus) :
    e.torus (p + q) = e.torus p + e.torus q := by
  obtain ⟨x, rfl⟩ := M.project_surjective p
  obtain ⟨y, rfl⟩ := M.project_surjective q
  rw [← M.project_add, e.project_eq, L.project_add, e.project_eq, e.project_eq]

def torusAddHom (e : PhysicalTorusEquiv L M) : Torus →+ Torus where
  toFun := e.torus
  map_zero' := e.torus_map_zero
  map_add' := e.torus_map_add

theorem measurePreserving_canonicalArea (e : PhysicalTorusEquiv L M) :
    MeasurePreserving e.torus canonicalArea canonicalArea := by
  exact AddMonoidHom.measurePreserving (f := e.torusAddHom)
    e.torus.continuous e.torus.surjective rfl

end MNEC.CutLatticeRebasing.PhysicalTorusEquiv

namespace MNEC.RebasedLatticeArea

open LatticeTorus PrimitiveLatticeRebasing CutLatticeRebasing MeasureTheory Set

theorem torusHomeomorph_measurePreserving (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    MeasurePreserving (torusHomeomorph m n h) (rebased L m n h).area L.area := by
  have hmp := (PhysicalTorusEquiv.primitive L m n h).measurePreserving_canonicalArea
  simpa only [Lattice.area, rebased_covolume, PhysicalTorusEquiv.primitive] using
    hmp.smul_measure (ENNReal.ofReal L.covolume)

theorem map_torusHomeomorph_area (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    Measure.map (torusHomeomorph m n h) (rebased L m n h).area = L.area :=
  (torusHomeomorph_measurePreserving L m n h).map_eq

theorem torusHomeomorph_area_preimage (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (V : Set Torus) :
    (rebased L m n h).area (torusHomeomorph m n h ⁻¹' V) = L.area V :=
  (torusHomeomorph_measurePreserving L m n h).measure_preimage_emb
    (torusHomeomorph m n h).measurableEmbedding V

theorem torusHomeomorph_area_image (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (V : Set Torus) :
    L.area (torusHomeomorph m n h '' V) = (rebased L m n h).area V := by
  have hp := torusHomeomorph_area_preimage L m n h (torusHomeomorph m n h '' V)
  rw [(torusHomeomorph m n h).injective.preimage_image] at hp
  exact hp.symm

end MNEC.RebasedLatticeArea

