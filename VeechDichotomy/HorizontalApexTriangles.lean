module

public import VeechDichotomy.HyperbolicTriangles

/-! Exact coordinate membership for the actual Euclidean convex hull
with a horizontal base and apex i. The reverse inclusion constructs
the literal base point and barycentric coefficients, including the
apex where the usual division formula is unavailable. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HorizontalApexTriangles

open Set

def planar (a b : ℝ) : Set ℂ := convexHull ℝ {(a : ℂ), (b : ℂ), Complex.I}

theorem horizontal_segment {a b : ℝ} (hab : a ≤ b) :
    segment ℝ (a : ℂ) (b : ℂ) = Complex.ofReal '' Icc a b := by
  have h := image_segment ℝ Complex.ofRealCLM.toLinearMap.toAffineMap a b
  rw [segment_eq_uIcc, uIcc_of_le hab] at h
  exact h.symm

theorem mem_iff {a b : ℝ} (hab : a ≤ b) (u : ℂ) :
    u ∈ planar a b ↔ 0 ≤ u.im ∧ u.im ≤ 1 ∧
      (1 - u.im) * a ≤ u.re ∧ u.re ≤ (1 - u.im) * b := by
  rw [planar, ← convexJoin_segment_singleton]
  constructor
  · intro hu
    obtain ⟨v, hv, w, hw, α, β, hα, hβ, hsum, rfl⟩ := mem_convexJoin.mp hu
    have hwI : w = Complex.I := hw
    subst w
    rw [horizontal_segment hab] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hre : (α • (x : ℂ) + β • Complex.I).re = α * x := by simp [Complex.real_smul]
    have him : (α • (x : ℂ) + β • Complex.I).im = β := by simp [Complex.real_smul]
    rw [hre, him]
    have hαeq : 1 - β = α := by linarith only [hsum]
    refine ⟨hβ, by linarith, ?_, ?_⟩
    · rw [hαeq]
      exact mul_le_mul_of_nonneg_left hx.1 hα
    · rw [hαeq]
      exact mul_le_mul_of_nonneg_left hx.2 hα
  · rintro ⟨hy₀, hy₁, hleft, hright⟩
    by_cases htop : u.im = 1
    · have hu : u = Complex.I := by
        apply Complex.ext
        · simp only [htop, sub_self, zero_mul, Complex.I_re] at hleft hright ⊢
          linarith
        · simpa using htop
      rw [hu]
      exact subset_convexJoin_right (by exact ⟨(a : ℂ), left_mem_segment ℝ _ _⟩) (by simp)
    · have hd : 0 < 1 - u.im := by
        have hlt : u.im < 1 := lt_of_le_of_ne hy₁ htop
        linarith
      let x : ℝ := u.re / (1 - u.im)
      have hx : x ∈ Icc a b := by
        constructor
        · apply (le_div_iff₀ hd).mpr
          nlinarith only [hleft]
        · apply (div_le_iff₀ hd).mpr
          nlinarith only [hright]
      have hbase : (x : ℂ) ∈ segment ℝ (a : ℂ) (b : ℂ) := by
        rw [horizontal_segment hab]
        exact ⟨x, hx, rfl⟩
      apply mem_convexJoin.mpr
      refine ⟨(x : ℂ), hbase, Complex.I, by simp, 1 - u.im, u.im, hd.le, hy₀, by ring, ?_⟩
      apply Complex.ext
      · simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
        dsimp only [x]
        field_simp [hd.ne']
      · simp [Complex.real_smul]

theorem convex_planar (a b : ℝ) : Convex ℝ (planar a b) := convex_convexHull ℝ _

end VeechDichotomy.HorizontalApexTriangles
