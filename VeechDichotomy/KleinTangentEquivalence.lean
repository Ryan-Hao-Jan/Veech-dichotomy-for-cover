module

public import VeechDichotomy.DirichletActiveCones
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual real linear map from Klein displacements to endpoint
tangents is invertible. Its explicit inverse proves both identities;
finite dimensionality supplies the genuine linear homeomorphism used
to transport closed cones and their interiors. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KleinTangentEquivalence

open HyperbolicKleinMap
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

abbrev forward (a : ℍ) : ℂ →ₗ[ℝ] ℂ := HyperbolicTriangleAngleAddition.linear a

def inverse (a : ℍ) : ℂ →ₗ[ℝ] ℂ where
  toFun u := ⟨u.re - a.re * (2 * (a.im * u.im + a.re * u.re) / denominator a),
    2 * (a.im * u.im + a.re * u.re) / denominator a⟩
  map_add' u v := by apply Complex.ext <;> simp <;> ring
  map_smul' s u := by apply Complex.ext <;> simp [Complex.real_smul] <;> ring

theorem forward_re (a : ℍ) (u : ℂ) : (forward a u).re = u.re + a.re * u.im := rfl
theorem forward_im (a : ℍ) (u : ℂ) :
    (forward a u).im = (-a.re * u.re + (denominator a / 2 - a.re ^ 2) * u.im) / a.im := rfl
theorem inverse_re (a : ℍ) (u : ℂ) :
    (inverse a u).re = u.re - a.re * (2 * (a.im * u.im + a.re * u.re) / denominator a) := rfl
theorem inverse_im (a : ℍ) (u : ℂ) :
    (inverse a u).im = 2 * (a.im * u.im + a.re * u.re) / denominator a := rfl

theorem inverse_forward (a : ℍ) (u : ℂ) : inverse a (forward a u) = u := by
  apply Complex.ext <;>
    simp only [inverse_re, inverse_im, forward_re, forward_im] <;>
    field_simp [(denominator_pos a).ne', a.im_ne_zero] <;> ring

theorem forward_inverse (a : ℍ) (u : ℂ) : forward a (inverse a u) = u := by
  apply Complex.ext <;>
    simp only [inverse_re, inverse_im, forward_re, forward_im] <;>
    field_simp [(denominator_pos a).ne', a.im_ne_zero] <;> ring

def equiv (a : ℍ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun := forward a
  invFun := inverse a
  map_add' := (forward a).map_add
  map_smul' := (forward a).map_smul
  left_inv := inverse_forward a
  right_inv := forward_inverse a

def homeomorph (a : ℍ) : ℂ ≃ₜ ℂ := (equiv a).toContinuousLinearEquiv.toHomeomorph

theorem homeomorph_apply (a : ℍ) (u : ℂ) : homeomorph a u = forward a u := rfl

theorem forward_injective (a : ℍ) : Function.Injective (forward a) := (equiv a).injective

theorem forward_eq_zero_iff (a : ℍ) (u : ℂ) : forward a u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    apply forward_injective a
    simpa only [map_zero] using hu
  · rintro rfl
    exact map_zero _

theorem isClosed_image (a : ℍ) {S : Set ℂ} (hS : IsClosed S) : IsClosed (forward a '' S) :=
  (homeomorph a).isClosedMap S hS

theorem image_interior (a : ℍ) (S : Set ℂ) :
    forward a '' interior S = interior (forward a '' S) := (homeomorph a).image_interior S

end VeechDichotomy.KleinTangentEquivalence
