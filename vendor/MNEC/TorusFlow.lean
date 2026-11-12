module

public import MNEC.LatticeTorusMeasure
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

/-!
# Actual directional translations on a lattice torus

The action is computed from the physical-plane quotient projection, and
its group laws and joint continuity are proved. This is a torus flow; the
directional flow on the connected-sum quotient is a further construction.
-/

namespace MNEC.TorusFlow

open LatticeTorus
open MeasureTheory

def translate (L : Lattice) (v : Plane) (t : ℝ) (p : Torus) : Torus :=
  p + L.project (t • v)

@[simp] theorem translate_zero (L : Lattice) (v : Plane) (p : Torus) :
    translate L v 0 p = p := by
  simp [translate]

theorem translate_add (L : Lattice) (v : Plane) (s t : ℝ) (p : Torus) :
    translate L v (s + t) p = translate L v s (translate L v t p) := by
  simp [translate, add_smul, add_comm, add_left_comm]

theorem translate_project (L : Lattice) (v : Plane) (t : ℝ) (x : Plane) :
    translate L v t (L.project x) = L.project (x + t • v) := by
  simp [translate]

theorem continuous_translate (L : Lattice) (v : Plane) :
    Continuous (fun q : ℝ × Torus => translate L v q.1 q.2) :=
  continuous_snd.add (L.continuous_project.comp (continuous_fst.smul continuous_const))

@[instance_reducible] def directionalAction (L : Lattice) (v : Plane) : AddAction ℝ Torus where
  vadd := translate L v
  zero_vadd := translate_zero L v
  add_vadd := translate_add L v

theorem translate_neg (L : Lattice) (v : Plane) (t : ℝ) (p : Torus) :
    translate L v (-t) (translate L v t p) = p := by
  rw [← translate_add, neg_add_cancel, translate_zero]

instance canonicalArea_isAddHaar : MeasureTheory.Measure.IsAddHaarMeasure canonicalArea := by
  unfold canonicalArea
  infer_instance

/-- The actual quotient translations preserve physical fundamental-cell
area, not just a separately assumed measure on the torus. -/
theorem translate_measurePreserving (L : Lattice) (v : Plane) (t : ℝ) :
    MeasurePreserving (translate L v t) L.area L.area := by
  exact (measurePreserving_add_right canonicalArea (L.project (t • v))).smul_measure
    (ENNReal.ofReal L.covolume)

end MNEC.TorusFlow
