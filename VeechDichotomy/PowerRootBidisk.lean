module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Separation.Connected
public import Jacobians.MappingDegree.IsPathConnectedBallMinusCountable
public import VeechDichotomy.AnalyticPowerBranchParameters

/-! A continuous family of roots of a fixed monomial is itself one
monomial near the zero section, provided one fiber is analytic. Analytic
order supplies divisibility; connectedness of the punctured bidisk and
finiteness of the root set remove all parameter-dependent branch choices. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PowerRootBidisk

open Set Filter Metric Topology
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem order_divides {f : ℂ → ℂ} {k l : ℕ} (hl : 0 < l) (hf : AnalyticAt ℂ f 0)
    (hpow : (fun z => f z ^ k) =ᶠ[𝓝 0] fun z => z ^ l) : ∃ r : ℕ, 0 < r ∧ l = r * k := by
  have horder : analyticOrderNatAt (f ^ k) 0 = analyticOrderNatAt ((id : ℂ → ℂ) ^ l) 0 :=
    congrArg ENat.toNat (analyticOrderAt_congr hpow)
  rw [analyticOrderNatAt_pow hf, analyticOrderNatAt_pow analyticAt_id] at horder
  have hid : analyticOrderNatAt (id : ℂ → ℂ) 0 = 1 := by simp [analyticOrderNatAt]
  simp only [hid, nsmul_eq_mul, mul_one] at horder
  refine ⟨analyticOrderNatAt f 0, Nat.pos_of_ne_zero ?_, ?_⟩
  · intro hr
    rw [hr, mul_zero] at horder
    exact hl.ne' horder.symm
  · exact horder.symm.trans (Nat.mul_comm _ _)

theorem roots_finite {k : ℕ} (hk : 0 < k) : {z : ℂ | z ^ k = 1}.Finite := by
  have h := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hk (1 : ℂ))
  simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] using h

theorem root_constant {E : Type*} [TopologicalSpace E] {S : Set E} (hS : IsPreconnected S)
    (f : E → ℂ) (hf : ContinuousOn f S) {k : ℕ} (hk : 0 < k) (hpow : ∀ x ∈ S, f x ^ k = 1)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have himage : IsPreconnected (f '' S) := hS.image f hf
  have hfinite : (f '' S).Finite := (roots_finite hk).subset (by
    rintro _ ⟨z, hz, rfl⟩
    exact hpow z hz)
  let : Finite (f '' S) := hfinite.to_subtype
  let : PreconnectedSpace (f '' S) := Subtype.preconnectedSpace himage
  let : Subsingleton (f '' S) := PreconnectedSpace.trivial_of_discrete
  exact congrArg Subtype.val (Subsingleton.elim (⟨f x, ⟨x, hx, rfl⟩⟩ : f '' S) ⟨f y, ⟨y, hy, rfl⟩⟩)

theorem monomial_on_bidisk (F : ℂ × ℂ → ℂ) (μ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hF : ContinuousOn F (ball μ a ×ˢ ball 0 b))
    (hpow : ∀ p ∈ ball μ a ×ˢ ball 0 b, F p ^ k = p.2 ^ l)
    (han : AnalyticAt ℂ (fun z => F (μ, z)) 0) :
    ∃ r : ℕ, 0 < r ∧ l = r * k ∧ ∃ c : ℂ, ∀ p ∈ ball μ a ×ˢ ball 0 b, F p = c * p.2 ^ r := by
  have hslice : (fun z => F (μ, z) ^ k) =ᶠ[𝓝 0] fun z => z ^ l := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hb] with z hz
    exact hpow (μ, z) ⟨mem_ball_self ha, hz⟩
  obtain ⟨r, hr, hlr⟩ := order_divides hl han hslice
  let S : Set (ℂ × ℂ) := ball μ a ×ˢ (ball 0 b \ {0})
  have hconn : IsPreconnected S := ((isPathConnected_ball ha).isConnected.prod
    (Jacobians.Discharge.Set.Countable.isPathConnected_ball_diff_complex hb (finite_singleton (0 : ℂ)).countable).isConnected).isPreconnected
  let g (p : ℂ × ℂ) := F p / p.2 ^ r
  have hsub : S ⊆ ball μ a ×ˢ ball 0 b := fun _ hp => ⟨hp.1, hp.2.1⟩
  have hg : ContinuousOn g S := (hF.mono hsub).div (continuous_snd.pow r).continuousOn
    (fun _ hp => pow_ne_zero r hp.2.2)
  have hgpow : ∀ p ∈ S, g p ^ k = 1 := by
    intro p hp
    change (F p / p.2 ^ r) ^ k = 1
    rw [div_pow, hpow p (hsub hp), ← pow_mul, ← hlr, div_self (pow_ne_zero l hp.2.2)]
  let z : ℂ := (b / 2 : ℝ)
  have hz : z ∈ ball (0 : ℂ) b := by
    rw [mem_ball, dist_zero_right]
    change ‖((b / 2 : ℝ) : ℂ)‖ < b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hb)]
    exact half_lt_self hb
  have hz0 : z ≠ 0 := Complex.ofReal_ne_zero.mpr (half_pos hb).ne'
  have href : (μ, z) ∈ S := ⟨mem_ball_self ha, hz, hz0⟩
  refine ⟨r, hr, hlr, g (μ, z), ?_⟩
  intro p hp
  by_cases hp0 : p.2 = 0
  · have hzero : F p = 0 := eq_zero_of_pow_eq_zero (by simpa only [hp0, zero_pow hl.ne'] using hpow p hp)
    rw [hzero, hp0, zero_pow hr.ne', mul_zero]
  · have hsame : g p = g (μ, z) := root_constant hconn g hg hk hgpow ⟨hp.1, hp.2, hp0⟩ href
    exact (div_eq_iff (pow_ne_zero r hp0)).mp hsame

theorem contDiffAt_of_power_germ (F : ℂ × ℂ → ℂ) (μ : ℂ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hF : ∀ᶠ p in 𝓝 (μ, 0), ContinuousAt F p)
    (hpow : ∀ᶠ p in 𝓝 (μ, 0), F p ^ k = p.2 ^ l)
    (han : AnalyticAt ℂ (fun z => F (μ, z)) 0) : ContDiffAt ℂ ω F (μ, 0) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hF.and hpow)
  have hsub : ball μ δ ×ˢ ball (0 : ℂ) δ ⊆ ball (μ, 0) δ := by
    intro p hp
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact hp
  obtain ⟨r, _, _, c, hmon⟩ := monomial_on_bidisk F μ hδ hδ hk hl
    (fun p hp => ((hball (hsub hp)).1).continuousWithinAt) (fun p hp => (hball (hsub hp)).2) han
  have hpoly : ContDiffAt ℂ ω (fun p : ℂ × ℂ => c * p.2 ^ r) (μ, 0) :=
    contDiffAt_const.mul (contDiffAt_snd.pow r)
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (show (μ, (0 : ℂ)) ∈ ball μ δ ×ˢ ball 0 δ from
    ⟨mem_ball_self hδ, mem_ball_self hδ⟩)] with p hp
  exact hmon p hp

end VeechDichotomy.PowerRootBidisk
