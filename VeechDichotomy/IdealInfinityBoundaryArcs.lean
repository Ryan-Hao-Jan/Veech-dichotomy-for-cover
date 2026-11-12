module

public import VeechDichotomy.DirichletIdealInfinity

/-! Actual unit-circle arcs approaching the Klein point at physical
infinity, and the exact signs of genuine distance half-planes on them.
The parameter sign distinguishes the two sides of that endpoint. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealInfinityBoundaryArcs

open Set Filter Topology HyperbolicKleinHalfPlanes HyperbolicBisectorNull DirichletIdealInfinity
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def arc (t : ℝ) : ℂ := ⟨2 * t / (1 + t ^ 2), (1 - t ^ 2) / (1 + t ^ 2)⟩

theorem denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem norm_arc (t : ℝ) : ‖arc t‖ = 1 := by
  have hs : Complex.normSq (arc t) = 1 := by
    simp only [arc, Complex.normSq_apply]
    field_simp [(denominator_pos t).ne']
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, hs, one_pow]

theorem arc_zero : arc 0 = Complex.I := by apply Complex.ext <;> norm_num [arc]

theorem arc_ne_I {t : ℝ} (ht : t ≠ 0) : arc t ≠ Complex.I := by
  intro he
  have hr := congrArg Complex.re he
  change 2 * t / (1 + t ^ 2) = 0 at hr
  exact mul_ne_zero (by norm_num) ht ((div_eq_zero_iff.mp hr).resolve_right (denominator_pos t).ne')

theorem arc_as_complex (t : ℝ) : arc t =
    ((2 * t / (1 + t ^ 2) : ℝ) : ℂ) + (((1 - t ^ 2) / (1 + t ^ 2) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp only [arc, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]

theorem continuous_arc : Continuous arc := by
  have he : arc = fun t : ℝ =>
      ((2 * t / (1 + t ^ 2) : ℝ) : ℂ) + (((1 - t ^ 2) / (1 + t ^ 2) : ℝ) : ℂ) * Complex.I :=
    funext arc_as_complex
  rw [he]
  fun_prop (disch := exact fun t => (denominator_pos t).ne')

theorem arc_tendsto (σ : ℝ) : Tendsto (fun t => arc (σ * t)) (𝓝 0) (𝓝 Complex.I) := by
  have hc : Continuous (fun t : ℝ => arc (σ * t)) :=
    continuous_arc.comp (show Continuous (fun t : ℝ => σ * t) by fun_prop)
  simpa only [mul_zero, arc_zero] using! (hc.continuousAt (x := (0 : ℝ))).tendsto

theorem affineForm_arc (p q : ℍ) (t : ℝ) : affineForm p q (arc t) =
    (leading p q + linear p q * t + constant p q * t ^ 2) / (1 + t ^ 2) := by
  simp only [affineForm, arc]
  field_simp [(denominator_pos t).ne']
  ring

theorem eventually_halfPlane (p q : ℍ) (σ : ℝ) (ha : leading p q ≤ 0)
    (hb : leading p q = 0 → σ * linear p q < 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → affineForm p q (arc (σ * t)) ≤ 0 := by
  rcases lt_or_eq_of_le ha with ha | he
  · have hc : Continuous (fun t : ℝ => affineForm p q (arc (σ * t))) := by
      have hf : Continuous (affineForm p q) := by unfold affineForm; fun_prop
      exact hf.comp (continuous_arc.comp (show Continuous (fun t : ℝ => σ * t) by fun_prop))
    have hval : affineForm p q (arc (σ * (0 : ℝ))) < 0 := by
      simpa only [mul_zero, arc_zero, affineForm_I, leading] using! ha
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), affineForm p q (arc (σ * t)) < 0 :=
      (isOpen_lt hc continuous_const).mem_nhds hval
    exact hev.mono (fun _ h _ => h.le)
  · have hc : Continuous (fun t : ℝ => σ * linear p q + σ ^ 2 * constant p q * t) := by fun_prop
    have hval : σ * linear p q + σ ^ 2 * constant p q * 0 < 0 := by simpa only [mul_zero, add_zero] using hb he
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), σ * linear p q + σ ^ 2 * constant p q * t < 0 :=
      (isOpen_lt hc continuous_const).mem_nhds hval
    filter_upwards [hev] with t ht hpos
    have hformula : affineForm p q (arc (σ * t)) =
        (t / (1 + (σ * t) ^ 2)) * (σ * linear p q + σ ^ 2 * constant p q * t) := by
      rw [affineForm_arc, he]
      ring
    rw [hformula]
    exact mul_nonpos_of_nonneg_of_nonpos (div_pos hpos (denominator_pos _)).le ht.le

end VeechDichotomy.IdealInfinityBoundaryArcs
