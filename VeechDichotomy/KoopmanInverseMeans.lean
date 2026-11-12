module

public import VeechDichotomy.KoopmanMeanShift

/-! Preserving inverse maps have inverse actual L2 Koopman operators,
the SAME fixed subspace and the SAME mean projection. The inverse
equations and projection identity are proved from actual compositions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KoopmanInverseMeans

open MeasureTheory Filter Topology KoopmanMeanErgodic

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f r : Ω → Ω)
  (hf : MeasurePreserving f μ μ) (hr : MeasurePreserving r μ μ)

theorem operator_inverse (hfr : ∀ x, f (r x) = x) (g : Space μ) :
    operator μ r hr (operator μ f hf g) = g := by
  apply Lp.ext
  change ⇑(Lp.compMeasurePreserving r hr (Lp.compMeasurePreserving f hf g)) =ᵐ[μ] ⇑g
  have houter := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving f hf g) hr
  have hinner := hr.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving g hf)
  filter_upwards [houter, hinner] with x hx hi
  calc
    _ = Lp.compMeasurePreserving f hf g (r x) := hx
    _ = g (f (r x)) := hi
    _ = g x := congrArg g (hfr x)

theorem fixed_subspace_eq (hfr : ∀ x, f (r x) = x) (hrf : ∀ x, r (f x) = x) :
    (operator μ f hf).eqLocus (1 : Space μ →L[ℝ] Space μ) =
      (operator μ r hr).eqLocus (1 : Space μ →L[ℝ] Space μ) := by
  ext g
  change operator μ f hf g = g ↔ operator μ r hr g = g
  constructor
  · intro hg
    have h := operator_inverse μ f r hf hr hfr g
    rwa [hg] at h
  · intro hg
    have h := operator_inverse μ r f hr hf hrf g
    rwa [hg] at h

private theorem projection_congr (S T : Submodule ℝ (Space μ)) [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (h : S = T) (g : Space μ) :
    (S.orthogonalProjectionOnto g : Space μ) = (T.orthogonalProjectionOnto g : Space μ) := by
  subst T
  rfl

theorem mean_eq (hfr : ∀ x, f (r x) = x) (hrf : ∀ x, r (f x) = x) (g : Space μ) :
    limit μ f hf g = limit μ r hr g := by
  unfold limit
  exact projection_congr μ _ _ (fixed_subspace_eq μ f r hf hr hfr hrf) g

end VeechDichotomy.KoopmanInverseMeans
