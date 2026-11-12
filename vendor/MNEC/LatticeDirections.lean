module

public import MNEC.LatticeTorus
public import MNEC.IrrationalChildren

@[expose] public section

/-!
# Actual lattice-period directions and rational frame coordinates

The equivalence below clears the two rational coordinate denominators to
produce a genuine nonzero integer period of the specified real lattice.
It does not identify a twisted torus with the auxiliary lattice in the paper.
-/

noncomputable section

namespace MNEC.LatticeDirections

open LatticeTorus


/-- A vector parallel to an actual nonzero period of the real lattice. -/
def PeriodDirection (L : Lattice) (w : Plane) : Prop :=
  ∃ z : ℤ × ℤ, z ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ w = r • L.period z

private theorem scale_eq_smul (a : ℝ) (v : Plane) : IrrationalChildren.scale a v = a • v := by
  rfl

/-- Clearing both denominators gives an actual integer vector, rather than
assuming that rational and integer directions agree. -/
private theorem clear_rational_vector (q : ℚ × ℚ) :
    ∃ d : ℝ, ∃ z : ℤ × ℤ, 0 < d ∧
      IrrationalChildren.castVector q = d⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)) := by
  let d : ℝ := (q.1.den : ℝ) * (q.2.den : ℝ)
  let z : ℤ × ℤ := (q.1.num * (q.2.den : ℤ), q.2.num * (q.1.den : ℤ))
  have h₁ : (0 : ℝ) < q.1.den := by exact_mod_cast q.1.den_pos
  have h₂ : (0 : ℝ) < q.2.den := by exact_mod_cast q.2.den_pos
  refine ⟨d, z, mul_pos h₁ h₂, ?_⟩
  apply Prod.ext <;> simp only [IrrationalChildren.castVector, Prod.smul_mk, smul_eq_mul]
  · dsimp [d, z]
    simp only [Rat.cast_def, Int.cast_mul, Int.cast_natCast]
    field_simp
  · dsimp [d, z]
    simp only [Rat.cast_def, Int.cast_mul, Int.cast_natCast]
    field_simp

theorem periodDirection_iff_rational_coordinates (L : Lattice) (w : Plane) :
    PeriodDirection L w ↔ IrrationalChildren.RationalDirection (L.frame.symm w) := by
  constructor
  · rintro ⟨z, hz, r, hr, rfl⟩
    refine ⟨r, ((z.1 : ℚ), (z.2 : ℚ)), hr, ?_, ?_⟩
    · intro hzero
      apply hz
      apply Prod.ext
      · have h : (z.1 : ℚ) = 0 := congrArg Prod.fst hzero
        exact_mod_cast h
      · have h : (z.2 : ℚ) = 0 := congrArg Prod.snd hzero
        exact_mod_cast h
    · simp only [map_smul, Lattice.period, ContinuousLinearEquiv.symm_apply_apply,
        scale_eq_smul, IrrationalChildren.castVector, Rat.cast_intCast]
  · rintro ⟨a, q, ha, hq, hw⟩
    obtain ⟨d, z, hd, hz⟩ := clear_rational_vector q
    have hzn : z ≠ 0 := by
      intro hzero
      apply hq
      have hcastzero : IrrationalChildren.castVector q = 0 := by
        simpa [hzero, ← Prod.zero_eq_mk] using hz
      apply Prod.ext
      · have h : (q.1 : ℝ) = 0 := congrArg Prod.fst hcastzero
        change q.1 = 0
        exact_mod_cast h
      · have h : (q.2 : ℝ) = 0 := congrArg Prod.snd hcastzero
        change q.2 = 0
        exact_mod_cast h
    refine ⟨z, hzn, a * d⁻¹, mul_ne_zero ha (inv_ne_zero (ne_of_gt hd)), ?_⟩
    apply L.frame.symm.injective
    rw [map_smul]
    simp only [Lattice.period, ContinuousLinearEquiv.symm_apply_apply]
    rw [hw, scale_eq_smul, hz, smul_smul]

def integerPeriodParameters (L : Lattice) (x y : Plane) : Set ℤ :=
  {t | PeriodDirection L (x + (t : ℝ) • y)}

theorem integerPeriodParameters_at_most_two (L : Lattice) (x y : Plane)
    (hxy : IrrationalChildren.cross (L.frame.symm x) (L.frame.symm y) ≠ 0)
    (hirr : ¬ IrrationalChildren.RationalDirection (L.frame.symm x)) :
    (integerPeriodParameters L x y).Finite ∧
      (integerPeriodParameters L x y).ncard ≤ 2 := by
  have hsets : integerPeriodParameters L x y =
      IrrationalChildren.integerParameters (L.frame.symm x) (L.frame.symm y) := by
    ext t
    change PeriodDirection L (x + (t : ℝ) • y) ↔
      IrrationalChildren.RationalDirection (IrrationalChildren.affine (L.frame.symm x) (L.frame.symm y) (t : ℝ))
    rw [periodDirection_iff_rational_coordinates]
    have hcoord : L.frame.symm (x + (t : ℝ) • y) =
        IrrationalChildren.affine (L.frame.symm x) (L.frame.symm y) (t : ℝ) := by
      ext <;> simp [map_add, map_smul, IrrationalChildren.affine]
    rw [hcoord]
  rw [hsets]
  exact IrrationalChildren.integerParameters_at_most_two hxy hirr

/-- The same result stated directly with irrationality relative to the actual lattice. -/
theorem actual_lattice_at_most_two (L : Lattice) (x y : Plane)
    (hxy : IrrationalChildren.cross (L.frame.symm x) (L.frame.symm y) ≠ 0)
    (hirr : ¬ PeriodDirection L x) :
    (integerPeriodParameters L x y).Finite ∧
      (integerPeriodParameters L x y).ncard ≤ 2 := by
  apply integerPeriodParameters_at_most_two L x y hxy
  exact fun h => hirr ((periodDirection_iff_rational_coordinates L x).2 h)

/-- The determinant transformation law, proved for every real linear map
of the plane by expanding its two standard-basis columns. -/
theorem cross_map (F : Plane →ₗ[ℝ] Plane) (x y : Plane) :
    IrrationalChildren.cross (F x) (F y) =
      IrrationalChildren.cross (F (1, 0)) (F (0, 1)) * IrrationalChildren.cross x y := by
  have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by ext <;> simp
  have hy : y = y.1 • (1, 0) + y.2 • (0, 1) := by ext <;> simp
  have hFx : F x = x.1 • F (1, 0) + x.2 • F (0, 1) := by
    calc
      F x = F (x.1 • (1, 0) + x.2 • (0, 1)) := congrArg F hx
      _ = x.1 • F (1, 0) + x.2 • F (0, 1) := by simp only [map_add, map_smul]
  have hFy : F y = y.1 • F (1, 0) + y.2 • F (0, 1) := by
    calc
      F y = F (y.1 • (1, 0) + y.2 • (0, 1)) := congrArg F hy
      _ = y.1 • F (1, 0) + y.2 • F (0, 1) := by simp only [map_add, map_smul]
  rw [hFx, hFy]
  change
    (x.1 * (F (1, 0)).1 + x.2 * (F (0, 1)).1) *
      (y.1 * (F (1, 0)).2 + y.2 * (F (0, 1)).2) -
    (x.1 * (F (1, 0)).2 + x.2 * (F (0, 1)).2) *
      (y.1 * (F (1, 0)).1 + y.2 * (F (0, 1)).1) =
    ((F (1, 0)).1 * (F (0, 1)).2 - (F (1, 0)).2 * (F (0, 1)).1) *
      (x.1 * y.2 - x.2 * y.1)
  ring

theorem frame_coordinates_cross_ne_zero (L : Lattice) (x y : Plane)
    (hxy : IrrationalChildren.cross x y ≠ 0) :
    IrrationalChildren.cross (L.frame.symm x) (L.frame.symm y) ≠ 0 := by
  intro hzero
  apply hxy
  have h := cross_map L.frame.toLinearMap (L.frame.symm x) (L.frame.symm y)
  simpa [hzero] using h

/-- The lattice version with independence checked directly in the physical plane. -/
theorem actual_lattice_at_most_two_of_physical_independence
    (L : Lattice) (x y : Plane) (hxy : IrrationalChildren.cross x y ≠ 0)
    (hirr : ¬ PeriodDirection L x) :
    (integerPeriodParameters L x y).Finite ∧
      (integerPeriodParameters L x y).ncard ≤ 2 :=
  actual_lattice_at_most_two L x y (frame_coordinates_cross_ne_zero L x y hxy) hirr

end MNEC.LatticeDirections

