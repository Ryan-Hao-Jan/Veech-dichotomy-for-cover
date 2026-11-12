module

public import VeechDichotomy.EffectiveCycleMultiplicity

/-! Actual equal-radius complex points are exposed, and the exposed-root
real slope key is injective on all other circle points. The proof uses
actual norm-square identities; a ray from one circle point meets that
circle in at most one further point. These are geometric inputs for
constructing the angular order of the actual nearest-site polygon. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircleExposedPoints

open Set

def functional (a : ℂ) : ℂ →L[ℝ] ℝ := InnerProductSpace.toDual ℝ ℂ a

theorem normSq_eq (a : ℂ) (R : ℝ) (ha : ‖a‖ = R) : Complex.normSq a = R ^ 2 := by
  rw [← Complex.sq_norm, ha]

theorem exposing_pair (a b : ℂ) (R : ℝ) (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hba : b ≠ a) :
    functional a b < functional a a := by
  have hA := normSq_eq a R ha
  have hB := normSq_eq b R hb
  have hdiff : 0 < Complex.normSq (a - b) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hba he.symm)))
  change inner ℝ a b < inner ℝ a a
  rw [DirichletSiteNormals.complex_inner, DirichletSiteNormals.complex_inner]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hA hB hdiff
  nlinarith only [hA, hB, hdiff]

theorem functional_ne_zero (a : ℂ) (R : ℝ) (ha : ‖a‖ = R) (hR : 0 < R) : functional a ≠ 0 := by
  intro he
  have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L a) he
  change inner ℝ a a = 0 at h
  have hne : a ≠ 0 := norm_pos_iff.mp (by rw [ha]; exact hR)
  exact (real_inner_self_pos.mpr hne).ne' h

theorem not_mem_hull_rest (V : Set ℂ) (R : ℝ) (hV : ∀ z ∈ V, ‖z‖ = R) (a : ℂ) (ha : a ∈ V) :
    a ∉ convexHull ℝ (V \ {a}) := by
  have hsub : V \ {a} ⊆ functional a ⁻¹' Iio (functional a a) := by
    intro b hb
    exact exposing_pair a b R (hV a ha) (hV b hb.1) (by simpa only [mem_singleton_iff] using hb.2)
  have hbound := convexHull_min hsub ((convex_Iio _).linear_preimage (functional a).toLinearMap)
  intro hp
  have he : functional a a < functional a a := hbound hp
  exact lt_irrefl _ he

theorem ray_unique (a u v : ℂ) (R : ℝ) (ha : ‖a‖ = R) (hu : ‖u‖ = R) (hv : ‖v‖ = R)
    (hua : u ≠ a) (k : ℝ) (hk : 0 < k) (he : v - a = k • (u - a)) : u = v := by
  have hvpoint : v = a + k • (u - a) := by
    calc
      v = a + (v - a) := by abel
      _ = _ := by rw [he]
  have hid : Complex.normSq v - k * Complex.normSq u + (k - 1) * Complex.normSq a =
      k * (k - 1) * Complex.normSq (u - a) := by
    rw [hvpoint]
    simp [Complex.normSq_apply, Complex.real_smul]
    ring
  have hz : k * (k - 1) * Complex.normSq (u - a) = 0 := by
    rw [normSq_eq a R ha, normSq_eq u R hu, normSq_eq v R hv] at hid
    nlinarith only [hid]
  have hdiff : 0 < Complex.normSq (u - a) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hua))
  have hkprod : k * (k - 1) = 0 := (mul_eq_zero.mp hz).resolve_right hdiff.ne'
  have hkone : k = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hkprod).resolve_left hk.ne')
  rw [hkone, one_smul] at he
  have hvu := congrArg (fun w : ℂ => w + a) he
  simp only [sub_add_cancel] at hvu
  exact hvu.symm

theorem slope_injective (V : Set ℂ) (R : ℝ) (hR : 0 < R) (hV : ∀ z ∈ V, ‖z‖ = R) (a : ℂ) (ha : a ∈ V) :
    InjOn (ExposedRootCoordinates.slope (functional a) a) (V \ {a}) := by
  intro u hu v hv he
  have hua : u ≠ a := by simpa only [mem_singleton_iff] using hu.2
  have hva : v ≠ a := by simpa only [mem_singleton_iff] using hv.2
  obtain ⟨k, hk, hray⟩ := ExposedRootCoordinates.equal_slope_rays (functional a)
    (functional_ne_zero a R (hV a ha) hR) a u v
    (exposing_pair a u R (hV a ha) (hV u hu.1) hua)
    (exposing_pair a v R (hV a ha) (hV v hv.1) hva) he
  exact ray_unique a u v R (hV a ha) (hV u hu.1) (hV v hv.1) hua k hk hray

end VeechDichotomy.CircleExposedPoints
