module

public import VeechDichotomy.NativeBeltramiCharts
public import VeechDichotomy.AnalyticPowerBranchParameters

/-! Joint analytic compatibility of the complex unit-disk deformation.
Primitive translation constants become c + mu * conj c. At regular
overlaps the actual continuous power branch is analytic by its explicit
one-variable local inverse; overlaps containing a zero are identities. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiTransitions

open MNEC.NativeAbelianDifferential NativeBeltramiCharts Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem transition_power_germ (q : Differential X) (i j : X) (p : ℂ × ℂ)
    (hp : p ∈ ((chart q i).symm.trans (chart q j)).source) :
    ∃ c : ℂ, ∀ᶠ r in 𝓝 p, (((chart q i).symm.trans (chart q j)) r).2 ^ (powerAt q j).exponent =
      r.2 ^ (powerAt q i).exponent + c + r.1 * star c := by
  let x := (chart q i).symm p
  have hxi := (chart_source q i x).mp ((chart q i).map_target hp.1)
  have hxj := (chart_source q j x).mp hp.2
  obtain ⟨c, hc⟩ := primitive_difference q i j x.2 hxi hxj
  have hcont : ContinuousAt (fun r : ℂ × ℂ => ((chart q i).symm r).2) p :=
    continuous_snd.continuousAt.comp ((chart q i).symm.continuousAt hp.1)
  refine ⟨c, ?_⟩
  filter_upwards [(chart q i).open_target.mem_nhds hp.1, hcont hc] with r hr hdiff
  have hparam : ((chart q i).symm r).1.val = r.1 := congrArg Prod.fst ((chart q i).right_inv hr)
  have hin : BeltramiPlane.map ((chart q i).symm r).1.val
      ((powerAt q i).chart ((chart q i).symm r).2 ^ (powerAt q i).exponent) = r.2 ^ (powerAt q i).exponent := by
    rw [← chart_power]
    exact congrArg (fun s : ℂ × ℂ => s.2 ^ (powerAt q i).exponent) ((chart q i).right_inv hr)
  change (chart q j ((chart q i).symm r)).2 ^ (powerAt q j).exponent = _
  rw [chart_power, hdiff]
  calc
    BeltramiPlane.map ((chart q i).symm r).1.val
        ((powerAt q i).chart ((chart q i).symm r).2 ^ (powerAt q i).exponent + c) =
      BeltramiPlane.map ((chart q i).symm r).1.val
        ((powerAt q i).chart ((chart q i).symm r).2 ^ (powerAt q i).exponent) + c +
          ((chart q i).symm r).1.val * star c := by
      simp only [BeltramiPlane.map, star_add, mul_add]
      ring
    _ = _ := by rw [hin, hparam]

theorem power_derivative_ne_zero (q : Differential X) (j : X) (x : BeltramiPlane.Parameter × X)
    (hx : x ∈ (chart q j).source) (hreg : x.2 ∈ regularSet q) :
    ((powerAt q j).exponent : ℂ) * (chart q j x).2 ^ ((powerAt q j).exponent - 1) ≠ 0 := by
  by_cases hz : (chart q j x).2 = 0
  · have heq := (chart_zero_iff q j x hx).mp hz
    have hj : j ∈ regularSet q := heq ▸ hreg
    have hk := (powerAt q j).regular_center_exponent_one hj
    simp only [hk, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, ne_eq, one_ne_zero, not_false_eq_true]
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr (powerAt q j).exponent_pos.ne') (pow_ne_zero _ hz)

theorem transition_contDiffAt (q : Differential X) (i j : X) (p : ℂ × ℂ)
    (hp : p ∈ ((chart q i).symm.trans (chart q j)).source) :
    ContDiffAt ℂ ω ((chart q i).symm.trans (chart q j)) p := by
  let x := (chart q i).symm p
  have hxi := (chart_source q i x).mp ((chart q i).map_target hp.1)
  have hxj := (chart_source q j x).mp hp.2
  by_cases hzero : x.2 ∈ zeroSet q
  · have hi : x.2 = i := (powerAt q i).zero_in_source_eq_center hxi hzero
    have hj : x.2 = j := (powerAt q j).zero_in_source_eq_center hxj hzero
    have hij : i = j := hi.symm.trans hj
    rw [← hij]
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [(chart q i).open_target.mem_nhds hp.1] with r hr
    exact (chart q i).right_inv hr
  · obtain ⟨c, hpow⟩ := transition_power_germ q i j p hp
    have hf : ContinuousAt (fun r : ℂ × ℂ => (((chart q i).symm.trans (chart q j)) r).2) p :=
      continuous_snd.continuousAt.comp (((chart q i).symm.trans (chart q j)).continuousAt hp)
    have hpoly : ContDiffAt ℂ ω (fun r : ℂ × ℂ => r.2 ^ (powerAt q i).exponent + c + r.1 * star c) p :=
      ((contDiffAt_snd.pow _).add contDiffAt_const).add (contDiffAt_fst.mul contDiffAt_const)
    have hpower : ContDiffAt ℂ ω
        (fun r : ℂ × ℂ => (((chart q i).symm.trans (chart q j)) r).2 ^ (powerAt q j).exponent) p :=
      hpoly.congr_of_eventuallyEq hpow
    have hroot := AnalyticPowerBranchParameters.contDiffAt_of_power hf hpower
      (power_derivative_ne_zero q j x hp.2 hzero)
    have hpair := contDiffAt_fst.prodMk hroot
    apply hpair.congr_of_eventuallyEq
    filter_upwards [(chart q i).open_target.mem_nhds hp.1] with r hr
    refine Prod.ext ?_ ?_
    · change ((chart q i).symm r).1.val = r.1
      exact congrArg Prod.fst ((chart q i).right_inv hr)
    · rfl

theorem transition_contDiffOn (q : Differential X) (i j : X) :
    ContDiffOn ℂ ω ((chart q i).symm.trans (chart q j)) ((chart q i).symm.trans (chart q j)).source :=
  fun p hp => (transition_contDiffAt q i j p hp).contDiffWithinAt

end VeechDichotomy.NativeBeltramiTransitions
