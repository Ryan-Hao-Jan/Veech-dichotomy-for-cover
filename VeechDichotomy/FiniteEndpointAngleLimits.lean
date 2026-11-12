module

public import VeechDichotomy.HyperbolicIntrinsicAngles

/-! The actual intrinsic corner angle tends to zero when its three
vertices approach distinct finite real endpoints. Multiplying genuine
endpoint directions by a positive scalar removes their singular
denominator; their limits are positive imaginary vectors. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteEndpointAngleLimits

open Filter Topology HyperbolicDirectionVectors HyperbolicIntrinsicAngles
open scoped UpperHalfPlane

def scaledDirection (a b : ℍ) : ℂ :=
  ⟨2 * a.im * (b.re - a.re), (b.re - a.re) ^ 2 + b.im ^ 2 - a.im ^ 2⟩

theorem scaledDirection_as_complex (a b : ℍ) : scaledDirection a b =
    ((2 * a.im * (b.re - a.re) : ℝ) : ℂ) +
      (((b.re - a.re) ^ 2 + b.im ^ 2 - a.im ^ 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp only [scaledDirection, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]

theorem scaledDirection_eq (a b : ℍ) : scaledDirection a b = (2 * a.im : ℝ) • direction a b := by
  apply Complex.ext
  · simp only [scaledDirection, Complex.smul_re, direction, smul_eq_mul]
  · simp only [scaledDirection, Complex.smul_im, direction, verticalCoefficient, smul_eq_mul]
    field_simp [a.im_ne_zero]

theorem angle_eq_scaled (a b c : ℍ) :
    angleAt a b c = InnerProductGeometry.angle (scaledDirection a b) (scaledDirection a c) := by
  rw [scaledDirection_eq, scaledDirection_eq,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (mul_pos (by norm_num) a.im_pos),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (mul_pos (by norm_num) a.im_pos)]
  rfl

theorem scaledDirection_tendsto {α : Type*} {l : Filter α} (A B : α → ℍ) (a b : ℝ)
    (ha : Tendsto (fun k => (A k).re) l (𝓝 a)) (hb : Tendsto (fun k => (B k).re) l (𝓝 b))
    (hai : Tendsto (fun k => (A k).im) l (𝓝 0)) (hbi : Tendsto (fun k => (B k).im) l (𝓝 0)) :
    Tendsto (fun k => scaledDirection (A k) (B k)) l (𝓝 (((b - a) ^ 2 : ℝ) • Complex.I)) := by
  have hr := ((tendsto_const_nhds (x := (2 : ℝ))).mul hai).mul (hb.sub ha)
  have hi := (((hb.sub ha).pow 2).add (hbi.pow 2)).sub (hai.pow 2)
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul_const Complex.I)
  simpa only [Function.comp_def, ← scaledDirection_as_complex, mul_zero, zero_mul,
    zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero, Complex.ofReal_zero, zero_add,
    Complex.real_smul] using! h

theorem angleAt_tendsto_zero {α : Type*} {l : Filter α} (A B C : α → ℍ) (a b c : ℝ)
    (ha : Tendsto (fun k => (A k).re) l (𝓝 a)) (hb : Tendsto (fun k => (B k).re) l (𝓝 b))
    (hc : Tendsto (fun k => (C k).re) l (𝓝 c))
    (hai : Tendsto (fun k => (A k).im) l (𝓝 0)) (hbi : Tendsto (fun k => (B k).im) l (𝓝 0))
    (hci : Tendsto (fun k => (C k).im) l (𝓝 0)) (hba : b ≠ a) (hca : c ≠ a) :
    Tendsto (fun k => angleAt (A k) (B k) (C k)) l (𝓝 0) := by
  have hp : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hba)
  have hq : 0 < (c - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hca)
  have hpn : ((b - a) ^ 2 : ℝ) • Complex.I ≠ 0 := smul_ne_zero hp.ne' Complex.I_ne_zero
  have hqn : ((c - a) ^ 2 : ℝ) • Complex.I ≠ 0 := smul_ne_zero hq.ne' Complex.I_ne_zero
  have h := (InnerProductGeometry.continuousAt_angle hpn hqn).tendsto.comp
    ((scaledDirection_tendsto A B a b ha hb hai hbi).prodMk_nhds
      (scaledDirection_tendsto A C a c ha hc hai hci))
  simpa only [Function.comp_def, ← angle_eq_scaled, InnerProductGeometry.angle_smul_left_of_pos _ _ hp,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hq,
    InnerProductGeometry.angle_self Complex.I_ne_zero] using! h

end VeechDichotomy.FiniteEndpointAngleLimits
