module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-! Rational-scale limits of monotone real functions control varying
real arguments at every continuity point of the limiting function.
This supplies the squeeze needed when the source orbit lengths depend
on the selected limiting rectangle vertices. -/

@[expose] public section

namespace VeechDichotomy.MonotoneRationalLimits

open Set Filter Topology

theorem varying_argument {I : Type*} {l : Filter I} (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hmono : ∀ᶠ i in l, Monotone (F i)) (hrows : ∀ q : ℚ, Tendsto (fun i => F i (q : ℝ)) l (𝓝 (f (q : ℝ))))
    {x : I → ℝ} {a : ℝ} (hx : Tendsto x l (𝓝 a)) (hf : ContinuousAt f a) :
    Tendsto (fun i => F i (x i)) l (𝓝 (f a)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hf (Ioi_mem_nhds hb))
    obtain ⟨q, hlow, hqa⟩ := exists_rat_btwn (sub_lt_self a hε)
    have hqball : (q : ℝ) ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hqa)]
      linarith
    have hbq : b < f (q : ℝ) := hsub hqball
    filter_upwards [hmono, hx (Ioi_mem_nhds hqa), hrows q (Ioi_mem_nhds hbq)] with i hiM hiX hiF
    have hxi : (q : ℝ) < x i := hiX
    have hfi : b < F i (q : ℝ) := hiF
    exact hfi.trans_le (hiM hxi.le)
  · intro b hb
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hf (Iio_mem_nhds hb))
    obtain ⟨q, haq, hupp⟩ := exists_rat_btwn (lt_add_of_pos_right a hε)
    have hqball : (q : ℝ) ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr haq)]
      linarith
    have hqb : f (q : ℝ) < b := hsub hqball
    filter_upwards [hmono, hx (Iio_mem_nhds haq), hrows q (Iio_mem_nhds hqb)] with i hiM hiX hiF
    have hxi : x i < (q : ℝ) := hiX
    have hfi : F i (q : ℝ) < b := hiF
    exact (hiM hxi.le).trans_lt hfi

end VeechDichotomy.MonotoneRationalLimits
