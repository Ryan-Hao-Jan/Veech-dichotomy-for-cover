module

public import VeechDichotomy.HorizontalApexTriangles

/-! Literal three-half-plane coordinates for a Euclidean triangle with
horizontal base and any apex in the upper half-plane. An explicit real
linear map and its inverse transport the already proved normalized
triangle membership formula; no barycentric or half-plane oracle remains. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EuclideanTriangleCoordinates

open Set

def lift (p : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM + Complex.imCLM.smulRight p

theorem lift_re (p z : ℂ) : (lift p z).re = z.re + z.im * p.re := by
  simp [lift, Complex.real_smul]

theorem lift_im (p z : ℂ) : (lift p z).im = z.im * p.im := by
  simp [lift, Complex.real_smul]

theorem lift_real (p : ℂ) (a : ℝ) : lift p (a : ℂ) = (a : ℂ) := by
  apply Complex.ext <;> simp [lift_re, lift_im]

theorem lift_I (p : ℂ) : lift p Complex.I = p := by
  apply Complex.ext <;> simp [lift_re, lift_im]

def back (p u : ℂ) : ℂ := ⟨u.re - u.im / p.im * p.re, u.im / p.im⟩

theorem lift_back (p u : ℂ) (hp : p.im ≠ 0) : lift p (back p u) = u := by
  apply Complex.ext
  · rw [lift_re]
    change u.re - u.im / p.im * p.re + u.im / p.im * p.re = u.re
    ring
  · rw [lift_im]
    exact div_mul_cancel₀ u.im hp

theorem back_lift (p z : ℂ) (hp : p.im ≠ 0) : back p (lift p z) = z := by
  apply Complex.ext
  · change (lift p z).re - (lift p z).im / p.im * p.re = z.re
    rw [lift_re, lift_im, mul_div_cancel_right₀ _ hp]
    ring
  · change (lift p z).im / p.im = z.im
    rw [lift_im, mul_div_cancel_right₀ _ hp]

theorem image_planar (p : ℂ) (a b : ℝ) :
    lift p '' HorizontalApexTriangles.planar a b = convexHull ℝ {(a : ℂ), (b : ℂ), p} := by
  change (lift p).toLinearMap '' convexHull ℝ {(a : ℂ), (b : ℂ), Complex.I} = _
  rw [(lift p).toLinearMap.image_convexHull]
  change convexHull ℝ (lift p '' {(a : ℂ), (b : ℂ), Complex.I}) = _
  simp only [image_insert_eq, image_singleton, lift_real, lift_I]

theorem mem_triangle_iff_back (p u : ℂ) (hp : p.im ≠ 0) (a b : ℝ) :
    u ∈ convexHull ℝ {(a : ℂ), (b : ℂ), p} ↔ back p u ∈ HorizontalApexTriangles.planar a b := by
  rw [← image_planar]
  constructor
  · rintro ⟨z, hz, he⟩
    rw [← he, back_lift p z hp]
    exact hz
  · intro hu
    exact ⟨back p u, hu, lift_back p u hp⟩

theorem mem_triangle_iff {a b : ℝ} (hab : a ≤ b) (p u : ℂ) (hp : 0 < p.im) :
    u ∈ convexHull ℝ {(a : ℂ), (b : ℂ), p} ↔
      0 ≤ u.im ∧ u.im ≤ p.im ∧
        (p.im - u.im) * a + u.im * p.re ≤ p.im * u.re ∧
        p.im * u.re ≤ (p.im - u.im) * b + u.im * p.re := by
  rw [mem_triangle_iff_back p u hp.ne' a b, HorizontalApexTriangles.mem_iff hab]
  change (0 ≤ u.im / p.im ∧ u.im / p.im ≤ 1 ∧
    (1 - u.im / p.im) * a ≤ u.re - u.im / p.im * p.re ∧
    u.re - u.im / p.im * p.re ≤ (1 - u.im / p.im) * b) ↔ _
  have hzero : 0 ≤ u.im / p.im ↔ 0 ≤ u.im := by rw [le_div_iff₀ hp, zero_mul]
  have hone : u.im / p.im ≤ 1 ↔ u.im ≤ p.im := by rw [div_le_iff₀ hp, one_mul]
  have hbase (x : ℝ) : p.im * ((1 - u.im / p.im) * x) = (p.im - u.im) * x := by
    field_simp [hp.ne']
  have hpoint : p.im * (u.re - u.im / p.im * p.re) = p.im * u.re - u.im * p.re := by
    field_simp [hp.ne']
  have hleft : (1 - u.im / p.im) * a ≤ u.re - u.im / p.im * p.re ↔
      (p.im - u.im) * a + u.im * p.re ≤ p.im * u.re := by
    calc
      _ ↔ p.im * ((1 - u.im / p.im) * a) ≤ p.im * (u.re - u.im / p.im * p.re) :=
        (mul_le_mul_iff_of_pos_left hp).symm
      _ ↔ _ := by rw [hbase, hpoint]; constructor <;> intro h <;> linarith
  have hright : u.re - u.im / p.im * p.re ≤ (1 - u.im / p.im) * b ↔
      p.im * u.re ≤ (p.im - u.im) * b + u.im * p.re := by
    calc
      _ ↔ p.im * (u.re - u.im / p.im * p.re) ≤ p.im * ((1 - u.im / p.im) * b) :=
        (mul_le_mul_iff_of_pos_left hp).symm
      _ ↔ _ := by rw [hbase, hpoint]; constructor <;> intro h <;> linarith
  rw [hzero, hone, hleft, hright]

theorem mem_triangle_iff_halfPlanes {a b : ℝ} (hab : a < b) (p u : ℂ) (hp : 0 < p.im) :
    u ∈ convexHull ℝ {(a : ℂ), (b : ℂ), p} ↔
      0 ≤ u.im ∧ (p.im - u.im) * a + u.im * p.re ≤ p.im * u.re ∧
        p.im * u.re ≤ (p.im - u.im) * b + u.im * p.re := by
  rw [mem_triangle_iff hab.le p u hp]
  constructor
  · rintro ⟨hy, _, hl, hr⟩
    exact ⟨hy, hl, hr⟩
  · rintro ⟨hy, hl, hr⟩
    have hprod : 0 ≤ (b - a) * (p.im - u.im) := by nlinarith only [hl, hr]
    have hupper : 0 ≤ p.im - u.im := (mul_nonneg_iff_of_pos_left (sub_pos.mpr hab)).mp hprod
    exact ⟨hy, by linarith, hl, hr⟩

end VeechDichotomy.EuclideanTriangleCoordinates
