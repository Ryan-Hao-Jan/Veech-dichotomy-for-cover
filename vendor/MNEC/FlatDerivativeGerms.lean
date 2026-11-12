module

public import MNEC.RemovableTranslationLine
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Identity derivatives supply the translation germs used at a removed line

The native mean-value theorem gives an actual translation on a small convex
ball from pointwise identity Frechet derivatives. Together with the proved
removable-line lemma, continuity then supplies the same translation across
the missing straight line. These are analytic criteria; the twist map's
pointwise hypotheses still have to be established in its actual charts.
-/

noncomputable section

namespace MNEC.FlatDerivativeGerms

open LatticeTorus Set Filter
open scoped Topology

theorem translation_germ_of_derivative_id (f : Plane → Plane) (U : Set Plane)
    (hU : IsOpen U) (hder : ∀ y ∈ U, HasFDerivAt f (ContinuousLinearMap.id ℝ Plane) y)
    (x : Plane) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, f y = y + (f x - x) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let c := f x - x
  let g : Plane → Plane := fun y => y + c
  have hf : DifferentiableOn ℝ f (Metric.ball x r) :=
    fun y hy => (hder y (hball hy)).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ g (Metric.ball x r) :=
    (differentiable_id.add_const c).differentiableOn
  have hdf : (Metric.ball x r).EqOn (fderivWithin ℝ f (Metric.ball x r))
      (fderivWithin ℝ g (Metric.ball x r)) := by
    intro y hy
    have hfy := (hder y (hball hy)).fderiv
    have hgy : fderiv ℝ g y = ContinuousLinearMap.id ℝ Plane :=
      ((hasFDerivAt_id y).add_const c).fderiv
    simpa only [fderivWithin_of_isOpen Metric.isOpen_ball hy] using hfy.trans hgy.symm
  have heq : (Metric.ball x r).EqOn f g :=
    (convex_ball x r).eqOn_of_fderivWithin_eq hf hg Metric.isOpen_ball.uniqueDiffOn hdf
      (Metric.mem_ball_self hr) (by dsimp [g, c]; abel)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with y hy
  exact heq hy

theorem removable_line_of_derivative_id (f : Plane → Plane) (ℓ : Plane →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (x : Plane) (r : ℝ) (hr : 0 < r)
    (hf : ContinuousOn f (Metric.ball x r))
    (hder : ∀ y ∈ Metric.ball x r, ℓ (y - x) ≠ 0 →
      HasFDerivAt f (ContinuousLinearMap.id ℝ Plane) y) :
    ∀ y ∈ Metric.ball x r, f y = y + (f x - x) := by
  let U : Set Plane := {y | y ∈ Metric.ball x r ∧ ℓ (y - x) ≠ 0}
  have hcont : Continuous (fun y : Plane => ℓ (y - x)) :=
    ℓ.continuous.comp (continuous_id.sub continuous_const)
  have hne : IsOpen {y : Plane | ℓ (y - x) ≠ 0} :=
    (isClosed_singleton.preimage hcont).isOpen_compl
  have hU : IsOpen U := Metric.isOpen_ball.inter hne
  apply RemovableTranslationLine.eq_translation_on_ball f ℓ hℓ x r hr hf
  intro y hy hline
  refine ⟨f y - y, ?_⟩
  exact translation_germ_of_derivative_id f U hU (fun p hp => hder p hp.1 hp.2) y ⟨hy, hline⟩

end MNEC.FlatDerivativeGerms

