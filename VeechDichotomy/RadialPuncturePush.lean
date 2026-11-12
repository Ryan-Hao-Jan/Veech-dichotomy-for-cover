module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Linarith

/-! A constructed radial homotopy of the punctured complex plane.
It pushes points outside a chosen disk, fixes the exterior throughout,
and stays inside every larger disk. This is the local building block
for a compact core of a finite-punctured native curve. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RadialPuncturePush

set_option backward.isDefEq.respectTransparency false

open Set Topology unitInterval

abbrev Punctured := {z : ℂ // z ≠ 0}

def push (r : ℝ) (t : I) (z : Punctured) : Punctured :=
  ⟨(max ‖z.val‖ ((t : ℝ) * r) / ‖z.val‖) • z.val, by
    have hn : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
    have ha : 0 < max ‖z.val‖ ((t : ℝ) * r) / ‖z.val‖ :=
      div_pos (lt_of_lt_of_le hn (le_max_left _ _)) hn
    exact smul_ne_zero ha.ne' z.property⟩

theorem continuous_push (r : ℝ) : Continuous (fun p : I × Punctured => push r p.1 p.2) := by
  apply Continuous.subtype_mk
  have hz : Continuous (fun p : I × Punctured => p.2.val) := continuous_subtype_val.comp continuous_snd
  have ht : Continuous (fun p : I × Punctured => (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  exact ((hz.norm.max (ht.mul continuous_const)).div hz.norm
    (fun p => norm_ne_zero_iff.mpr p.2.property)).smul hz

theorem push_zero (r : ℝ) (z : Punctured) : push r 0 z = z := by
  apply Subtype.ext
  change (max ‖z.val‖ ((0 : ℝ) * r) / ‖z.val‖) • z.val = z.val
  rw [zero_mul, max_eq_left (norm_nonneg _), div_self (norm_ne_zero_iff.mpr z.property), one_smul]

theorem norm_push (r : ℝ) (t : I) (z : Punctured) :
    ‖(push r t z).val‖ = max ‖z.val‖ ((t : ℝ) * r) := by
  have hn : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
  have ha : 0 ≤ max ‖z.val‖ ((t : ℝ) * r) / ‖z.val‖ :=
    (div_pos (lt_of_lt_of_le hn (le_max_left _ _)) hn).le
  change ‖(max ‖z.val‖ ((t : ℝ) * r) / ‖z.val‖) • z.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, div_mul_cancel₀ _ hn.ne']

theorem push_fixed_of_norm_ge {r : ℝ} (hr : 0 ≤ r) (t : I) (z : Punctured)
    (hz : r ≤ ‖z.val‖) : push r t z = z := by
  apply Subtype.ext
  have htr : (t : ℝ) * r ≤ ‖z.val‖ :=
    (mul_le_mul_of_nonneg_right t.property.2 hr).trans (by simpa only [one_mul] using hz)
  change (max ‖z.val‖ ((t : ℝ) * r) / ‖z.val‖) • z.val = z.val
  rw [max_eq_left htr, div_self (norm_ne_zero_iff.mpr z.property), one_smul]

theorem norm_push_one_ge (r : ℝ) (z : Punctured) : r ≤ ‖(push r 1 z).val‖ := by
  rw [norm_push]
  change r ≤ max ‖z.val‖ ((1 : ℝ) * r)
  rw [one_mul]
  exact le_max_right _ _

theorem norm_push_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (t : I) (z : Punctured)
    (hz : ‖z.val‖ ≤ R) : ‖(push r t z).val‖ ≤ R := by
  rw [norm_push]
  apply max_le hz
  have ht := mul_le_mul_of_nonneg_right t.property.2 hr
  have ht' : (t : ℝ) * r ≤ r := by simpa only [one_mul] using ht
  exact ht'.trans hrR

def endpoint (r : ℝ) : C(Punctured, Punctured) :=
  ⟨push r 1, (continuous_push r).comp (continuous_const.prodMk continuous_id)⟩

def homotopy (r : ℝ) : (ContinuousMap.id Punctured).Homotopy (endpoint r) where
  toContinuousMap := ⟨fun p => push r p.1 p.2, continuous_push r⟩
  map_zero_left := push_zero r
  map_one_left _ := rfl

def formula (r : ℝ) (t : I) (z : ℂ) : ℂ := (max ‖z‖ ((t : ℝ) * r) / ‖z‖) • z

theorem formula_eq_val (r : ℝ) (t : I) (z : Punctured) : formula r t z.val = (push r t z).val := rfl

theorem continuousAt_formula (r : ℝ) (t : I) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun p : I × ℂ => formula r p.1 p.2) (t, z) := by
  have hn : ContinuousAt (fun p : I × ℂ => ‖p.2‖) (t, z) := continuousAt_snd.norm
  have ht : ContinuousAt (fun p : I × ℂ => (p.1 : ℝ)) (t, z) :=
    continuous_subtype_val.continuousAt.comp continuousAt_fst
  exact ((hn.max (ht.mul continuousAt_const)).div hn (norm_ne_zero_iff.mpr hz)).smul continuousAt_snd

theorem formula_fixed_of_norm_ge {r : ℝ} (hr : 0 ≤ r) (t : I) {z : ℂ} (hz : z ≠ 0)
    (hznorm : r ≤ ‖z‖) : formula r t z = z :=
  congrArg Subtype.val (push_fixed_of_norm_ge hr t ⟨z, hz⟩ hznorm)

theorem norm_formula (r : ℝ) (t : I) {z : ℂ} (hz : z ≠ 0) :
    ‖formula r t z‖ = max ‖z‖ ((t : ℝ) * r) := norm_push r t ⟨z, hz⟩

theorem formula_mem_of_closedBall_subset {r : ℝ} (hr : 0 ≤ r) (t : I) {T : Set ℂ}
    (hT : Metric.closedBall 0 r ⊆ T) {z : ℂ} (hz : z ∈ T) (hz0 : z ≠ 0) : formula r t z ∈ T := by
  by_cases hnorm : r ≤ ‖z‖
  · rw [formula_fixed_of_norm_ge hr t hz0 hnorm]
    exact hz
  · apply hT
    have hnorm' : ‖z‖ ≤ r := (lt_of_not_ge hnorm).le
    have hpush := norm_push_le hr le_rfl t (⟨z, hz0⟩ : Punctured) hnorm'
    change ‖formula r t z‖ ≤ r at hpush
    simpa only [Metric.mem_closedBall, dist_zero_right] using hpush

end VeechDichotomy.RadialPuncturePush
