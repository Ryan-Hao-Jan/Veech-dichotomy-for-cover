module

public import VeechDichotomy.CirclePolygonOrder

/-! The actual angular width of the positive cone between two
positively ordered complex rays is exactly their actual angle.
Determinant cases order any two cone vectors; the proved Euclidean
angle-addition equality bounds their angle by the endpoint angle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PositiveConeAngleWidth

open Set ComplexOrientedTriangles HyperbolicRegionAngles
open scoped NNReal

def cone (a b : ℂ) : Set ℂ := {x | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x = α • a + β • b}

theorem cross_add_left (a b c : ℂ) : cross (a + b) c = cross a c + cross b c := by simp [cross]; ring
theorem cross_smul_left (r : ℝ) (a b : ℂ) : cross (r • a) b = r * cross a b := by
  simp [cross, Complex.real_smul]; ring
theorem cross_swap (a b : ℂ) : cross a b = -cross b a := by unfold cross; ring
theorem cross_self (a : ℂ) : cross a a = 0 := by unfold cross; ring

theorem mem_span {a b x : ℂ} (hx : x ∈ cone a b) : x ∈ Submodule.span ℝ≥0 {a, b} := by
  obtain ⟨α, β, hα, hβ, he⟩ := hx
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α, hα⟩, ⟨β, hβ⟩, ?_⟩
  simpa only [NNReal.smul_def] using! he.symm

theorem cross_right_nonneg {a b x : ℂ} (hD : 0 < cross a b) (hx : x ∈ cone a b) : 0 ≤ cross x b := by
  obtain ⟨α, β, hα, _, rfl⟩ := hx
  rw [cross_add_left, cross_smul_left, cross_smul_left, cross_self, mul_zero, add_zero]
  exact mul_nonneg hα hD.le

theorem right_edge_ray {a b x : ℂ} (hD : 0 < cross a b) (hx : x ∈ cone a b) (hne : x ≠ 0)
    (hzero : cross x b = 0) : ∃ r : ℝ, 0 < r ∧ x = r • b := by
  obtain ⟨α, β, hα, hβ, he⟩ := hx
  have hprod : α * cross a b = 0 := by
    rw [he, cross_add_left, cross_smul_left, cross_smul_left, cross_self, mul_zero, add_zero] at hzero
    exact hzero
  have hαzero : α = 0 := (mul_eq_zero.mp hprod).resolve_right hD.ne'
  have hxβ : x = β • b := by simpa only [hαzero, zero_smul, zero_add] using he
  have hβne : β ≠ 0 := by intro hz; rw [hz, zero_smul] at hxβ; exact hne hxβ
  exact ⟨β, lt_of_le_of_ne hβ (fun he => hβne he.symm), hxβ⟩

theorem ordered_angle_bound {a b x y : ℂ} (hD : 0 < cross a b) (hx : x ∈ cone a b) (hy : y ∈ cone a b)
    (hxn : x ≠ 0) (hyn : y ≠ 0) (hxy : 0 ≤ cross x y) :
    InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle a b := by
  have hxb := cross_right_nonneg hD hx
  by_cases hz : cross x b = 0
  · obtain ⟨r, hr, hxr⟩ := right_edge_ray hD hx hxn hz
    have hry : 0 ≤ r * cross b y := by simpa only [hxr, cross_smul_left] using hxy
    have hby : 0 ≤ cross b y :=
      (mul_le_mul_iff_of_pos_left hr).mp (by simpa only [mul_zero] using hry)
    have hyb := cross_right_nonneg hD hy
    rw [cross_swap b y] at hby
    have hyzero : cross y b = 0 := by linarith
    obtain ⟨s, hs, hys⟩ := right_edge_ray hD hy hyn hyzero
    have hbne : b ≠ 0 := by intro he; rw [he] at hD; simp [cross] at hD
    rw [hxr, hys, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs, InnerProductGeometry.angle_self hbne]
    exact InnerProductGeometry.angle_nonneg _ _
  · have hxbpos : 0 < cross x b := lt_of_le_of_ne hxb (fun he => hz he.symm)
    have hyspan : y ∈ Submodule.span ℝ≥0 {x, b} :=
      ComplexPositiveCones.mem_span x b y hxbpos hxy (cross_right_nonneg hD hy)
    have h₁ := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hxn (mem_span hx)
    have h₂ := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hyn hyspan
    linarith [InnerProductGeometry.angle_nonneg a x, InnerProductGeometry.angle_nonneg y b]

theorem angle_bound {a b x y : ℂ} (hD : 0 < cross a b) (hx : x ∈ cone a b) (hy : y ∈ cone a b)
    (hxn : x ≠ 0) (hyn : y ≠ 0) : InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle a b := by
  by_cases hxy : 0 ≤ cross x y
  · exact ordered_angle_bound hD hx hy hxn hyn hxy
  · have hyx : 0 ≤ cross y x := by rw [cross_swap]; exact neg_nonneg.mpr (le_of_not_ge hxy)
    rw [InnerProductGeometry.angle_comm x y]
    exact ordered_angle_bound hD hy hx hyn hxn hyx

theorem width_eq {a b : ℂ} (hD : 0 < cross a b) : vectorWidth (cone a b) = InnerProductGeometry.angle a b := by
  have hane : a ≠ 0 := by intro he; rw [he] at hD; simp [cross] at hD
  have hbne : b ≠ 0 := by intro he; rw [he] at hD; simp [cross] at hD
  have ha : a ∈ cone a b := ⟨1, 0, zero_le_one, le_rfl, by simp⟩
  have hb : b ∈ cone a b := ⟨0, 1, le_rfl, zero_le_one, by simp⟩
  apply le_antisymm
  · apply csSup_le (vectorValues_nonempty _)
    rintro θ (hz | ⟨x, y, hx, hy, hxn, hyn, rfl⟩)
    · have he : θ = 0 := hz
      rw [he]
      exact InnerProductGeometry.angle_nonneg _ _
    · exact angle_bound hD hx hy hxn hyn
  · exact le_csSup (vectorValues_bddAbove _) (Or.inr ⟨a, b, ha, hb, hane, hbne, rfl⟩)

end VeechDichotomy.PositiveConeAngleWidth
