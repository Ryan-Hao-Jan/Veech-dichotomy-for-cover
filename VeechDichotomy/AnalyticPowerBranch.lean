module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! A continuous branch whose positive power is analytic is analytic at
every point where that power has nonzero derivative in the branch value.
The analytic inverse is constructed by the inverse function theorem.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.AnalyticPowerBranch

open Filter Topology

theorem analyticAt_of_analytic_postcomp {f g : ℂ → ℂ} {a : ℂ}
    (hf : ContinuousAt f a) (hg : AnalyticAt ℂ g (f a))
    (hd : deriv g (f a) ≠ 0) (hgf : AnalyticAt ℂ (g ∘ f) a) :
    AnalyticAt ℂ f a := by
  let L := hg.hasStrictDerivAt.localInverse g (deriv g (f a)) (f a) hd
  have hL : AnalyticAt ℂ L (g (f a)) := hg.analyticAt_localInverse hd
  have hleft : ∀ᶠ y in 𝓝 (f a), L (g y) = y :=
    hg.hasStrictDerivAt.eventually_left_inverse hd
  have heq : f =ᶠ[𝓝 a] L ∘ g ∘ f := by
    filter_upwards [hf hleft] with z hz
    exact hz.symm
  have hcomp : AnalyticAt ℂ (L ∘ (g ∘ f)) a := AnalyticAt.comp (f := g ∘ f) hL hgf
  exact hcomp.congr heq.symm

theorem analyticAt_of_power {f : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hf : ContinuousAt f a) (hpow : AnalyticAt ℂ (fun z => f z ^ k) a)
    (hd : (k : ℂ) * f a ^ (k - 1) ≠ 0) : AnalyticAt ℂ f a := by
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ k) (f a) := analyticAt_id.pow k
  have hder : deriv (fun z : ℂ => z ^ k) (f a) = (k : ℂ) * f a ^ (k - 1) := by
    have h : HasDerivAt (fun z : ℂ => z ^ k) ((k : ℂ) * f a ^ (k - 1)) (f a) := by
      simpa only [id_eq, mul_one] using! (hasDerivAt_id (f a)).pow k
    exact h.deriv
  exact analyticAt_of_analytic_postcomp hf hp (hder ▸ hd) hpow

end VeechDichotomy.AnalyticPowerBranch
