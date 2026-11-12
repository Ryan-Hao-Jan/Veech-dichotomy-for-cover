module

public import VeechDichotomy.DirichletIdealRadialPoints

/-! Finite real endpoints of the actual Klein unit circle, with the single
point corresponding to infinity removed. The coordinate is injective; the
two reconstruction identities are explicit algebraic identities. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealBoundaryCoordinates

open Set

theorem normSq_eq_one {u : ℂ} (hu : ‖u‖ = 1) : Complex.normSq u = 1 := by
  rw [Complex.normSq_eq_norm_sq, hu]
  norm_num

theorem denominator_pos {u : ℂ} (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) : 0 < 1 - u.im := by
  have hi : u.im ≤ 1 := by simpa only [hu] using Complex.im_le_norm u
  have hs := normSq_eq_one hu
  rw [Complex.normSq_apply] at hs
  have hne : u.im ≠ 1 := by
    intro he
    have hr : u.re = 0 := by nlinarith [sq_nonneg u.re]
    exact hI (Complex.ext (by simpa using hr) (by simpa using he))
  exact sub_pos.mpr (lt_of_le_of_ne hi hne)

def endpoint (u : ℂ) : ℝ := u.re / (1 - u.im)

theorem endpoint_square {u : ℂ} (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) :
    endpoint u ^ 2 + 1 = 2 / (1 - u.im) := by
  have hd := (denominator_pos hu hI).ne'
  have hs := normSq_eq_one hu
  rw [Complex.normSq_apply] at hs
  unfold endpoint
  field_simp [hd]
  nlinarith only [hs]

theorem re_reconstruction {u : ℂ} (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) :
    u.re = 2 * endpoint u / (endpoint u ^ 2 + 1) := by
  rw [endpoint_square hu hI]
  unfold endpoint
  field_simp [(denominator_pos hu hI).ne']

theorem im_reconstruction {u : ℂ} (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) :
    u.im = (endpoint u ^ 2 - 1) / (endpoint u ^ 2 + 1) := by
  have he := endpoint_square hu hI
  have hs : endpoint u ^ 2 - 1 = 2 / (1 - u.im) - 2 := by linarith only [he]
  rw [hs, he]
  field_simp [(denominator_pos hu hI).ne']
  ring

theorem endpoint_injective {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huI : u ≠ Complex.I) (hvI : v ≠ Complex.I) (he : endpoint u = endpoint v) : u = v := by
  apply Complex.ext
  · rw [re_reconstruction hu huI, re_reconstruction hv hvI, he]
  · rw [im_reconstruction hu huI, im_reconstruction hv hvI, he]

end VeechDichotomy.IdealBoundaryCoordinates
