module

public import VeechDichotomy.AnalyticPowerBranch

/-! Parameter-dependent analytic roots are obtained by composing a
joint analytic power expression with its ONE-VARIABLE analytic local
inverse. No several-variable root-existence premise is added. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.AnalyticPowerBranchParameters

open Filter Topology
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem contDiffAt_of_analytic_postcomp {f : E → ℂ} {g : ℂ → ℂ} {a : E}
    (hf : ContinuousAt f a) (hg : AnalyticAt ℂ g (f a)) (hd : deriv g (f a) ≠ 0)
    (hgf : ContDiffAt ℂ ω (g ∘ f) a) : ContDiffAt ℂ ω f a := by
  let L := hg.hasStrictDerivAt.localInverse g (deriv g (f a)) (f a) hd
  have hL : AnalyticAt ℂ L (g (f a)) := hg.analyticAt_localInverse hd
  have hleft : ∀ᶠ y in 𝓝 (f a), L (g y) = y := hg.hasStrictDerivAt.eventually_left_inverse hd
  have heq : f =ᶠ[𝓝 a] L ∘ g ∘ f := by
    filter_upwards [hf hleft] with z hz
    exact hz.symm
  exact (hL.contDiffAt.comp a hgf).congr_of_eventuallyEq heq

theorem contDiffAt_of_power {f : E → ℂ} {a : E} {k : ℕ} (hf : ContinuousAt f a)
    (hpow : ContDiffAt ℂ ω (fun z => f z ^ k) a) (hd : (k : ℂ) * f a ^ (k - 1) ≠ 0) :
    ContDiffAt ℂ ω f a := by
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ k) (f a) := analyticAt_id.pow k
  have hder : deriv (fun z : ℂ => z ^ k) (f a) = (k : ℂ) * f a ^ (k - 1) := by
    exact ((hasDerivAt_id (f a)).pow k).deriv.trans (by simp only [id_eq, mul_one])
  exact contDiffAt_of_analytic_postcomp hf hp (hder ▸ hd) hpow

end VeechDichotomy.AnalyticPowerBranchParameters
