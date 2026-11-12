module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Three rational projective points on an affine line

This is the coordinate algebra behind the at-most-two rational children
argument. It does not identify torus rationality with the projective condition
used here; that geometric identification is a separate obligation.
-/

namespace MNEC.IrrationalChildren

abbrev Plane := ℝ × ℝ

def cross (v w : Plane) : ℝ := v.1 * w.2 - v.2 * w.1
def rationalCross (v w : ℚ × ℚ) : ℚ := v.1 * w.2 - v.2 * w.1
def castVector (q : ℚ × ℚ) : Plane := ((q.1 : ℝ), (q.2 : ℝ))
def scale (a : ℝ) (v : Plane) : Plane := (a * v.1, a * v.2)
def affine (x y : Plane) (t : ℝ) : Plane := (x.1 + t * y.1, x.2 + t * y.2)

/-- A nonzero real vector parallel to a nonzero vector with rational coordinates. -/
def RationalDirection (v : Plane) : Prop :=
  ∃ a : ℝ, ∃ q : ℚ × ℚ, a ≠ 0 ∧ q ≠ 0 ∧ v = scale a (castVector q)

theorem cross_affine (x y : Plane) (t s : ℝ) :
    cross (affine x y t) (affine x y s) = (s - t) * cross x y := by
  simp only [cross, affine]
  ring

theorem cross_scale (a b : ℝ) (v w : Plane) :
    cross (scale a v) (scale b w) = a * b * cross v w := by
  simp only [cross, scale]
  ring

theorem cross_castVector (q r : ℚ × ℚ) :
    cross (castVector q) (castVector r) = (rationalCross q r : ℝ) := by
  simp [cross, castVector, rationalCross]

theorem cross_ne_zero_affine {x y : Plane} (hxy : cross x y ≠ 0)
    {s t : ℚ} (hst : s ≠ t) :
    cross (affine x y (s : ℝ)) (affine x y (t : ℝ)) ≠ 0 := by
  rw [cross_affine]
  apply mul_ne_zero _ hxy
  apply sub_ne_zero.2
  intro h
  exact hst (Rat.cast_injective h.symm)

/-- Three distinct rational parameters with rational projective directions force
the starting vector to have a rational projective direction. -/
theorem rationalDirection_of_three {x y : Plane} (hxy : cross x y ≠ 0)
    {t₀ t₁ t₂ : ℚ} (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂)
    (h₀ : RationalDirection (affine x y (t₀ : ℝ)))
    (h₁ : RationalDirection (affine x y (t₁ : ℝ)))
    (h₂ : RationalDirection (affine x y (t₂ : ℝ))) : RationalDirection x := by
  obtain ⟨a₀, q₀, ha₀, hq₀, hu₀⟩ := h₀
  obtain ⟨a₁, q₁, ha₁, hq₁, hu₁⟩ := h₁
  obtain ⟨a₂, q₂, ha₂, hq₂, hu₂⟩ := h₂
  have hq₁₂ : rationalCross q₁ q₂ ≠ 0 := by
    intro hzero
    have h := cross_ne_zero_affine hxy h₁₂
    rw [hu₁, hu₂, cross_scale, cross_castVector, hzero] at h
    simp at h
  let r : ℚ := (t₂ - t₀) / (t₁ - t₀)
  have hr : r ≠ 0 := div_ne_zero (sub_ne_zero.2 h₀₂.symm) (sub_ne_zero.2 h₀₁.symm)
  have hden : (t₁ : ℝ) - (t₀ : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.2 h₀₁.symm)
  have hrreal : (r : ℝ) * ((t₁ : ℝ) - (t₀ : ℝ)) = (t₂ : ℝ) - (t₀ : ℝ) := by
    dsimp [r]
    push_cast
    field_simp
  have hu₂linear :
      affine x y (t₂ : ℝ) =
        ((1 - (r : ℝ)) * (affine x y (t₀ : ℝ)).1 + (r : ℝ) * (affine x y (t₁ : ℝ)).1,
         (1 - (r : ℝ)) * (affine x y (t₀ : ℝ)).2 + (r : ℝ) * (affine x y (t₁ : ℝ)).2) := by
    apply Prod.ext <;> simp only [affine]
    · nlinarith [congrArg (fun z => z * y.1) hrreal]
    · nlinarith [congrArg (fun z => z * y.2) hrreal]
  have hcrosszero : cross (affine x y (t₂ : ℝ)) (castVector q₂) = 0 := by
    rw [hu₂]
    simp [cross, scale]
    ring
  have hscaleeq :
      (1 - (r : ℝ)) * a₀ * (rationalCross q₀ q₂ : ℝ) +
        (r : ℝ) * a₁ * (rationalCross q₁ q₂ : ℝ) = 0 := by
    rw [hu₂linear, hu₀, hu₁] at hcrosszero
    simp only [cross, scale, castVector, rationalCross] at hcrosszero ⊢
    push_cast
    nlinarith [hcrosszero]
  let k : ℚ := -((1 - r) * rationalCross q₀ q₂) / (r * rationalCross q₁ q₂)
  have hkn : (r : ℝ) * (rationalCross q₁ q₂ : ℝ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero hr hq₁₂)
  have ha₁eq : a₁ = a₀ * (k : ℝ) := by
    dsimp [k]
    push_cast
    field_simp
    nlinarith [hscaleeq]
  let q : ℚ × ℚ :=
    ((t₁ * q₀.1 - t₀ * k * q₁.1) / (t₁ - t₀),
     (t₁ * q₀.2 - t₀ * k * q₁.2) / (t₁ - t₀))
  have hxrepr : x = scale a₀ (castVector q) := by
    have hx₀ := congrArg Prod.fst hu₀
    have hx₁ := congrArg Prod.fst hu₁
    have hy₀ := congrArg Prod.snd hu₀
    have hy₁ := congrArg Prod.snd hu₁
    simp only [affine, scale, castVector] at hx₀ hx₁ hy₀ hy₁
    rw [ha₁eq] at hx₁ hy₁
    apply Prod.ext <;> simp only [scale, castVector]
    · dsimp [q]
      push_cast
      field_simp
      nlinarith [congrArg (fun z => z * (t₁ : ℝ)) hx₀,
        congrArg (fun z => z * (t₀ : ℝ)) hx₁]
    · dsimp [q]
      push_cast
      field_simp
      nlinarith [congrArg (fun z => z * (t₁ : ℝ)) hy₀,
        congrArg (fun z => z * (t₀ : ℝ)) hy₁]
  refine ⟨a₀, q, ha₀, ?_, hxrepr⟩
  intro hq
  rw [hq] at hxrepr
  apply hxy
  rw [hxrepr]
  simp [scale, castVector, cross]

private theorem finite_ncard_le_two_of_no_three {α : Type*} (S : Set α)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → False) :
    S.Finite ∧ S.ncard ≤ 2 := by
  classical
  by_cases hs : S.Subsingleton
  · refine ⟨hs.finite, ?_⟩
    exact ((Set.ncard_le_one hs.finite).2 hs).trans (by norm_num)
  · obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.1 hs
    have hsub : S ⊆ {a, b} := by
      intro c hc
      by_cases hca : c = a
      · simp [hca]
      by_cases hcb : c = b
      · simp [hcb]
      exact (h a ha b hb c hc hab (Ne.symm hca) (Ne.symm hcb)).elim
    have hfin : ({a, b} : Set α).Finite := (Set.finite_singleton b).insert a
    refine ⟨hfin.subset hsub, ?_⟩
    exact (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_pair hab).le

def rationalParameters (x y : Plane) : Set ℚ :=
  {t | RationalDirection (affine x y (t : ℝ))}

theorem rationalParameters_at_most_two {x y : Plane}
    (hxy : cross x y ≠ 0) (hirr : ¬ RationalDirection x) :
    (rationalParameters x y).Finite ∧ (rationalParameters x y).ncard ≤ 2 := by
  apply finite_ncard_le_two_of_no_three
  intro a ha b hb c hc hab hac hbc
  exact hirr (rationalDirection_of_three hxy hab hac hbc ha hb hc)

def integerParameters (x y : Plane) : Set ℤ :=
  {t | RationalDirection (affine x y (t : ℝ))}

/-- The form used for integer twist families: at most two children are rational. -/
theorem integerParameters_at_most_two {x y : Plane}
    (hxy : cross x y ≠ 0) (hirr : ¬ RationalDirection x) :
    (integerParameters x y).Finite ∧ (integerParameters x y).ncard ≤ 2 := by
  obtain ⟨hfin, hcard⟩ := rationalParameters_at_most_two hxy hirr
  have hmap : ∀ t ∈ integerParameters x y, (t : ℚ) ∈ rationalParameters x y := by
    intro t ht
    simpa [integerParameters, rationalParameters] using ht
  have hinj : Set.InjOn (fun t : ℤ => (t : ℚ)) (integerParameters x y) := by
    intro a _ b _ hab
    exact Int.cast_injective hab
  refine ⟨?_, (Set.ncard_le_ncard_of_injOn _ hmap hinj hfin).trans hcard⟩
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨t, ht, rfl⟩
    exact hmap t ht)) hinj

end MNEC.IrrationalChildren
