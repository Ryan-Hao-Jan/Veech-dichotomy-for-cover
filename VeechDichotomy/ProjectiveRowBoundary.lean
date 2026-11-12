module

public import VeechDichotomy.IdealBoundaryCoordinates

/-! A nonzero real row determines an actual unit-circle endpoint.
Equal endpoints imply proportional rows; this is proved directly in
coordinates, with the point at infinity treated separately. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ProjectiveRowBoundary

def point (c d : ℝ) : ℂ := ⟨-2 * c * d / (c ^ 2 + d ^ 2), (d ^ 2 - c ^ 2) / (c ^ 2 + d ^ 2)⟩

theorem norm_point (c d : ℝ) (hd : 0 < c ^ 2 + d ^ 2) : ‖point c d‖ = 1 := by
  have hs : Complex.normSq (point c d) = 1 := by
    simp only [point, Complex.normSq_apply]
    field_simp [hd.ne']
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, hs, one_pow]

theorem point_eq_I_iff (c d : ℝ) (hd : 0 < c ^ 2 + d ^ 2) : point c d = Complex.I ↔ c = 0 := by
  constructor
  · intro he
    have hi := congrArg Complex.im he
    change (d ^ 2 - c ^ 2) / (c ^ 2 + d ^ 2) = 1 at hi
    have hm := (div_eq_one_iff_eq hd.ne').mp hi
    nlinarith only [hm, sq_nonneg c]
  · intro hc
    apply Complex.ext
    · simp only [point, hc, mul_zero, zero_mul, zero_div, Complex.I_re]
    · change (d ^ 2 - c ^ 2) / (c ^ 2 + d ^ 2) = 1
      apply (div_eq_one_iff_eq hd.ne').mpr
      rw [hc]
      ring

theorem endpoint_point (c d : ℝ) (_hd : 0 < c ^ 2 + d ^ 2) (hc : c ≠ 0) :
    IdealBoundaryCoordinates.endpoint (point c d) = -d / c := by
  change (-2 * c * d / (c ^ 2 + d ^ 2)) / (1 - (d ^ 2 - c ^ 2) / (c ^ 2 + d ^ 2)) = -d / c
  field_simp [_hd.ne', hc]
  have hcancel : c ^ 2 * c⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  linear_combination -d * hcancel

theorem proportional_of_point_eq (c d e f : ℝ) (hd : 0 < c ^ 2 + d ^ 2) (hf : 0 < e ^ 2 + f ^ 2)
    (he : point c d = point e f) : c * f - d * e = 0 := by
  by_cases hc : c = 0
  · have hp : point e f = Complex.I := he.symm.trans ((point_eq_I_iff c d hd).mpr hc)
    have hzero := (point_eq_I_iff e f hf).mp hp
    rw [hc, hzero]
    ring
  · have hn : e ≠ 0 := by
      intro hz
      have hp : point c d = Complex.I := he.trans ((point_eq_I_iff e f hf).mpr hz)
      exact hc ((point_eq_I_iff c d hd).mp hp)
    have h := congrArg IdealBoundaryCoordinates.endpoint he
    rw [endpoint_point c d hd hc, endpoint_point e f hf hn] at h
    field_simp [hc, hn] at h
    nlinarith only [h]

end VeechDichotomy.ProjectiveRowBoundary
