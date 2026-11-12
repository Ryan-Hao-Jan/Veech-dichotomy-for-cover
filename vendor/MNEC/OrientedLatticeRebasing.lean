module

public import MNEC.SurfaceRebasingArea
public import MNEC.Twists
public import MNEC.LatticeDirections

@[expose] public section

/-!
# Computed positive orientation for an arbitrary physical lattice

Swapping the two coordinate periods reverses the frame determinant but
preserves its absolute value and the entire physical lattice. A computed
case split therefore normalizes every actual frame to positive orientation.
The coordinate, cut and glued-surface homeomorphisms and their physical area
identities are derived from the actual swap; no orientation or area oracle
is supplied.
-/

noncomputable section

namespace MNEC.OrientedLatticeRebasing

open LatticeTorus CutTorus CutLatticeRebasing SurfaceLatticeRebasing MeasureTheory Set

theorem linearMap_det_eq_cross (F : Plane →ₗ[ℝ] Plane) :
    LinearMap.det F = Twists.cross (F (1, 0)) (F (0, 1)) := by
  have hF : F = Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![(F (1, 0)).1, (F (0, 1)).1; (F (1, 0)).2, (F (0, 1)).2] := by
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin_finTwoProd_apply]
    have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by ext <;> simp
    calc
      F x = F (x.1 • (1, 0) + x.2 • (0, 1)) := congrArg F hx
      _ = x.1 • F (1, 0) + x.2 • F (0, 1) := by simp only [map_add, map_smul]
      _ = _ := by ext <;> simp [mul_comm]
  calc
    LinearMap.det F = LinearMap.det
      (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        !![(F (1, 0)).1, (F (0, 1)).1; (F (1, 0)).2, (F (0, 1)).2]) :=
      congrArg LinearMap.det hF
    _ = Twists.cross (F (1, 0)) (F (0, 1)) := by
      rw [LinearMap.det_toLin, Matrix.det_fin_two]
      simp only [Twists.cross, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring

theorem period_cross_eq_det (L : Lattice) :
    Twists.cross (L.period (1, 0)) (L.period (0, 1)) =
      LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) := by
  simpa [Lattice.period] using (linearMap_det_eq_cross (L.frame : Plane →ₗ[ℝ] Plane)).symm

theorem cross_first_period_eq_det_mul_coordinate (L : Lattice) (w : Plane) :
    Twists.cross (L.period (1, 0)) w =
      LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) * (L.frame.symm w).2 := by
  have h := LatticeDirections.cross_map (L.frame : Plane →ₗ[ℝ] Plane)
    (1, 0) (L.frame.symm w)
  change Twists.cross (L.frame (1, 0)) (L.frame (L.frame.symm w)) =
    Twists.cross (L.frame (1, 0)) (L.frame (0, 1)) * Twists.cross (1, 0) (L.frame.symm w) at h
  have hd : Twists.cross (L.frame (1, 0)) (L.frame (0, 1)) =
      LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) := by
    simpa only [Lattice.period, Int.cast_one, Int.cast_zero] using period_cross_eq_det L
  rw [ContinuousLinearEquiv.apply_symm_apply, hd] at h
  simpa [Lattice.period, Twists.cross] using h

def swapLinear : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ

@[simp] theorem swapLinear_apply (x : Plane) : swapLinear x = x.swap := rfl

@[simp] theorem swapLinear_symm_apply (x : Plane) : swapLinear.symm x = x.swap := rfl

theorem swapLinear_det : LinearMap.det (swapLinear : Plane →ₗ[ℝ] Plane) = -1 := by
  rw [linearMap_det_eq_cross]
  norm_num [swapLinear, Twists.cross]

def swapLattice (L : Lattice) : Lattice where
  frame := swapLinear.trans L.frame

@[simp] theorem swapLattice_period (L : Lattice) (z : ℤ × ℤ) :
    (swapLattice L).period z = L.period z.swap := rfl

@[simp] theorem swapLattice_first_period (L : Lattice) :
    (swapLattice L).period (1, 0) = L.period (0, 1) := rfl

@[simp] theorem swapLattice_second_period (L : Lattice) :
    (swapLattice L).period (0, 1) = L.period (1, 0) := rfl

@[simp] theorem swapLattice_coordinates (L : Lattice) (x : Plane) :
    (swapLattice L).frame.symm x = (L.frame.symm x).swap := rfl

theorem swapLattice_period_range (L : Lattice) :
    range (swapLattice L).period = range L.period := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, rfl⟩

theorem swapLattice_det (L : Lattice) :
    LinearMap.det ((swapLattice L).frame : Plane →ₗ[ℝ] Plane) =
      -LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) := by
  change LinearMap.det ((L.frame : Plane →ₗ[ℝ] Plane).comp
    (swapLinear : Plane →ₗ[ℝ] Plane)) = _
  rw [LinearMap.det_comp, swapLinear_det, mul_neg_one]

theorem swapLattice_covolume (L : Lattice) : (swapLattice L).covolume = L.covolume := by
  rw [Lattice.covolume, swapLattice_det, abs_neg]
  rfl

def swapTorusHomeomorph : Torus ≃ₜ Torus := Homeomorph.prodComm UnitAddCircle UnitAddCircle

@[simp] theorem swapTorusHomeomorph_apply (p : Torus) : swapTorusHomeomorph p = p.swap := rfl

theorem swapTorusHomeomorph_project (L : Lattice) (x : Plane) :
    swapTorusHomeomorph ((swapLattice L).project x) = L.project x := rfl

def swapPhysicalEquiv (L : Lattice) : PhysicalTorusEquiv L (swapLattice L) where
  torus := swapTorusHomeomorph
  project_eq := swapTorusHomeomorph_project L

theorem swapTorusHomeomorph_measurePreserving (L : Lattice) :
    MeasurePreserving swapTorusHomeomorph (swapLattice L).area L.area := by
  have hMP := (swapPhysicalEquiv L).measurePreserving_canonicalArea
  simpa only [Lattice.area, swapLattice_covolume, swapPhysicalEquiv] using
    hMP.smul_measure (ENNReal.ofReal L.covolume)

theorem map_swapTorusHomeomorph_area (L : Lattice) :
    Measure.map swapTorusHomeomorph (swapLattice L).area = L.area :=
  (swapTorusHomeomorph_measurePreserving L).map_eq

def oriented (L : Lattice) : Lattice :=
  if LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) < 0 then swapLattice L else L

def orientedPhysicalEquiv (L : Lattice) : PhysicalTorusEquiv L (oriented L) := by
  unfold oriented
  split_ifs
  · exact swapPhysicalEquiv L
  · exact PhysicalTorusEquiv.refl L

theorem oriented_det_pos (L : Lattice) :
    0 < LinearMap.det ((oriented L).frame : Plane →ₗ[ℝ] Plane) := by
  have hdet : LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.frame.toLinearEquiv).ne_zero
  by_cases hneg : LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) < 0
  · rw [oriented, ite_eq_left hneg, swapLattice_det]
    exact neg_pos.mpr hneg
  · rw [oriented, ite_eq_right hneg]
    exact lt_of_le_of_ne (le_of_not_gt hneg) hdet.symm

theorem oriented_period_cross_pos (L : Lattice) :
    0 < Twists.cross ((oriented L).period (1, 0)) ((oriented L).period (0, 1)) := by
  rw [period_cross_eq_det]
  exact oriented_det_pos L

theorem oriented_period_range (L : Lattice) : range (oriented L).period = range L.period := by
  unfold oriented
  split_ifs
  · exact swapLattice_period_range L
  · rfl

def orientedPeriodCoordinates (L : Lattice) (z : ℤ × ℤ) : ℤ × ℤ :=
  if LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) < 0 then z.swap else z

theorem oriented_period_coordinates (L : Lattice) (z : ℤ × ℤ) :
    (oriented L).period (orientedPeriodCoordinates L z) = L.period z := by
  unfold oriented orientedPeriodCoordinates
  split_ifs <;> rfl

theorem orientedPeriodCoordinates_primitive (L : Lattice) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n) :
    PrimitiveLatticeRebasing.Primitive (orientedPeriodCoordinates L (m, n)).1
      (orientedPeriodCoordinates L (m, n)).2 := by
  unfold orientedPeriodCoordinates
  split_ifs
  · change Int.gcd n m = 1
    rw [Int.gcd_comm]
    exact h
  · exact h

theorem oriented_covolume (L : Lattice) : (oriented L).covolume = L.covolume := by
  unfold oriented
  split_ifs
  · exact swapLattice_covolume L
  · rfl

theorem oriented_covolume_eq_det (L : Lattice) :
    (oriented L).covolume = LinearMap.det ((oriented L).frame : Plane →ₗ[ℝ] Plane) :=
  abs_of_pos (oriented_det_pos L)

theorem oriented_embeddedSlit_iff (L : Lattice) (w : Plane) :
    (oriented L).EmbeddedSlit w ↔ L.EmbeddedSlit w := by
  let e := orientedPhysicalEquiv L
  constructor
  · intro he s t hst
    apply he
    apply e.torus.injective
    simpa only [e.arc_eq] using hst
  · intro he s t hst
    apply he
    simpa only [e.arc_eq] using congrArg e.torus hst

theorem oriented_measurePreserving (L : Lattice) :
    MeasurePreserving (orientedPhysicalEquiv L).torus (oriented L).area L.area := by
  have hMP := (orientedPhysicalEquiv L).measurePreserving_canonicalArea
  simpa only [Lattice.area, oriented_covolume] using
    hMP.smul_measure (ENNReal.ofReal L.covolume)

theorem map_oriented_area (L : Lattice) :
    Measure.map (orientedPhysicalEquiv L).torus (oriented L).area = L.area :=
  (oriented_measurePreserving L).map_eq

open PrimitiveLatticeRebasing

/-- A positive frame whose first generator is the specified primitive
physical period in the original, arbitrarily oriented lattice. -/
def orientedPrimitive (L : Lattice) (m n : ℤ) (h : Primitive m n) : Lattice :=
  rebased (oriented L) (orientedPeriodCoordinates L (m, n)).1
    (orientedPeriodCoordinates L (m, n)).2 (orientedPeriodCoordinates_primitive L m n h)

theorem primitive_rebased_det (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    LinearMap.det ((rebased L m n h).frame : Plane →ₗ[ℝ] Plane) =
      LinearMap.det (L.frame : Plane →ₗ[ℝ] Plane) := by
  change LinearMap.det ((L.frame : Plane →ₗ[ℝ] Plane).comp
    (realBasisChange m n h : Plane →ₗ[ℝ] Plane)) = _
  rw [LinearMap.det_comp, RebasedLatticeArea.realBasisChange_det, mul_one]

theorem orientedPrimitive_first_period (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    (orientedPrimitive L m n h).period (1, 0) = L.period (m, n) := by
  rw [orientedPrimitive, rebased_first_period]
  exact oriented_period_coordinates L (m, n)

theorem orientedPrimitive_det_pos (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    0 < LinearMap.det ((orientedPrimitive L m n h).frame : Plane →ₗ[ℝ] Plane) := by
  rw [orientedPrimitive, primitive_rebased_det]
  exact oriented_det_pos L

theorem orientedPrimitive_period_cross_pos (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    0 < Twists.cross ((orientedPrimitive L m n h).period (1, 0))
      ((orientedPrimitive L m n h).period (0, 1)) := by
  rw [period_cross_eq_det]
  exact orientedPrimitive_det_pos L m n h

theorem orientedPrimitive_period_range (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    range (orientedPrimitive L m n h).period = range L.period := by
  rw [orientedPrimitive, rebased_period_range, oriented_period_range]

theorem orientedPrimitive_covolume (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    (orientedPrimitive L m n h).covolume = L.covolume := by
  rw [orientedPrimitive, RebasedLatticeArea.rebased_covolume, oriented_covolume]

theorem orientedPrimitive_det_eq_covolume (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    LinearMap.det ((orientedPrimitive L m n h).frame : Plane →ₗ[ℝ] Plane) = L.covolume := by
  calc
    _ = (orientedPrimitive L m n h).covolume :=
      (abs_of_pos (orientedPrimitive_det_pos L m n h)).symm
    _ = L.covolume := orientedPrimitive_covolume L m n h

theorem orientedPrimitive_transverse_pos (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (hcross : 0 < Twists.cross (L.period (m, n)) w) :
    0 < ((orientedPrimitive L m n h).frame.symm w).2 := by
  have hformula := cross_first_period_eq_det_mul_coordinate (orientedPrimitive L m n h) w
  rw [orientedPrimitive_first_period] at hformula
  have hprod : 0 < LinearMap.det ((orientedPrimitive L m n h).frame : Plane →ₗ[ℝ] Plane) *
      ((orientedPrimitive L m n h).frame.symm w).2 := hformula ▸ hcross
  exact (mul_pos_iff_of_pos_left (orientedPrimitive_det_pos L m n h)).mp hprod

theorem orientedPrimitive_transverse_le_one (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (hcross : Twists.cross (L.period (m, n)) w ≤ L.covolume) :
    ((orientedPrimitive L m n h).frame.symm w).2 ≤ 1 := by
  have hformula := cross_first_period_eq_det_mul_coordinate (orientedPrimitive L m n h) w
  rw [orientedPrimitive_first_period, orientedPrimitive_det_eq_covolume] at hformula
  have hprod : L.covolume * ((orientedPrimitive L m n h).frame.symm w).2 ≤ L.covolume :=
    hformula ▸ hcross
  exact (mul_le_mul_iff_right₀ L.covolume_pos).mp (by simpa only [mul_one] using hprod)

theorem orientedPrimitive_transverse_lt_one (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (hcross : Twists.cross (L.period (m, n)) w < L.covolume) :
    ((orientedPrimitive L m n h).frame.symm w).2 < 1 := by
  have hformula := cross_first_period_eq_det_mul_coordinate (orientedPrimitive L m n h) w
  rw [orientedPrimitive_first_period, orientedPrimitive_det_eq_covolume] at hformula
  have hprod : L.covolume * ((orientedPrimitive L m n h).frame.symm w).2 < L.covolume :=
    hformula ▸ hcross
  exact (mul_lt_mul_iff_right₀ L.covolume_pos).mp (by simpa only [mul_one] using hprod)

theorem orientedPrimitive_transverse_bounds (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (hcross : 0 < Twists.cross (L.period (m, n)) w)
    (harea : Twists.cross (L.period (m, n)) w ≤ L.covolume) :
    0 < ((orientedPrimitive L m n h).frame.symm w).2 ∧
      ((orientedPrimitive L m n h).frame.symm w).2 ≤ 1 :=
  ⟨orientedPrimitive_transverse_pos L m n h w hcross,
    orientedPrimitive_transverse_le_one L m n h w harea⟩

theorem orientedPrimitive_transverse_mem_Ioo (L : Lattice) (m n : ℤ) (h : Primitive m n)
    (w : Plane) (hcross : 0 < Twists.cross (L.period (m, n)) w)
    (harea : Twists.cross (L.period (m, n)) w < L.covolume) :
    ((orientedPrimitive L m n h).frame.symm w).2 ∈ Ioo (0 : ℝ) 1 :=
  ⟨orientedPrimitive_transverse_pos L m n h w hcross,
    orientedPrimitive_transverse_lt_one L m n h w harea⟩

def orientedPrimitivePhysicalEquiv (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    PhysicalTorusEquiv L (orientedPrimitive L m n h) := by
  let c := orientedPeriodCoordinates L (m, n)
  let hc := orientedPeriodCoordinates_primitive L m n h
  exact
    { torus := (torusHomeomorph c.1 c.2 hc).trans (orientedPhysicalEquiv L).torus
      project_eq := fun x => by
        change (orientedPhysicalEquiv L).torus
          (torusHomeomorph c.1 c.2 hc ((rebased (oriented L) c.1 c.2 hc).project x)) = _
        rw [torusHomeomorph_project, (orientedPhysicalEquiv L).project_eq] }

theorem orientedPrimitive_measurePreserving (L : Lattice) (m n : ℤ) (h : Primitive m n) :
    MeasurePreserving (orientedPrimitivePhysicalEquiv L m n h).torus
      (orientedPrimitive L m n h).area L.area := by
  dsimp only [orientedPrimitivePhysicalEquiv, orientedPrimitive]
  exact (oriented_measurePreserving L).comp
    (RebasedLatticeArea.torusHomeomorph_measurePreserving (oriented L)
      (orientedPeriodCoordinates L (m, n)).1 (orientedPeriodCoordinates L (m, n)).2
      (orientedPeriodCoordinates_primitive L m n h))

def orientedCutHomeomorph (L : Lattice) (w : Plane) : Point (oriented L) w ≃ₜ Point L w :=
  (orientedPhysicalEquiv L).cutHomeomorph w

@[simp] theorem orientedCutHomeomorph_upper_project (L : Lattice) (w x : Plane) :
    orientedCutHomeomorph L w (upper (oriented L) w ((oriented L).project x)) =
      upper L w (L.project x) :=
  (orientedPhysicalEquiv L).cutHomeomorph_upper_project w x

def orientedSurfaceHomeomorph (L₁ L₂ : Lattice) (w : Plane) :
    SlitConnectedSum.Surface (oriented L₁) (oriented L₂) w ≃ₜ SlitConnectedSum.Surface L₁ L₂ w :=
  surfaceHomeomorph (orientedPhysicalEquiv L₁) (orientedPhysicalEquiv L₂) w

theorem orientedSurfaceHomeomorph_measurePreserving (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    MeasurePreserving (orientedSurfaceHomeomorph L₁ L₂ w)
      (ConnectedSumArea.area (oriented L₁) (oriented L₂) w) (ConnectedSumArea.area L₁ L₂ w) :=
  SurfaceRebasingArea.surfaceHomeomorph_measurePreserving
    (orientedPhysicalEquiv L₁) (orientedPhysicalEquiv L₂) w hw
    (oriented_measurePreserving L₁) (oriented_measurePreserving L₂)

theorem map_orientedSurfaceHomeomorph_area (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    Measure.map (orientedSurfaceHomeomorph L₁ L₂ w)
      (ConnectedSumArea.area (oriented L₁) (oriented L₂) w) = ConnectedSumArea.area L₁ L₂ w :=
  (orientedSurfaceHomeomorph_measurePreserving L₁ L₂ w hw).map_eq

end MNEC.OrientedLatticeRebasing

