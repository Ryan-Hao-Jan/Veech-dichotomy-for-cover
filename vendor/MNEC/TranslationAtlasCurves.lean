module

public import MNEC.TranslationAtlasField
public import MNEC.MaximalFlowAction

/-!
# Actual local and maximal native curves for a translation atlas

The native field is the independently constructed smooth pullback field.
Local chart inverses of physical lines are proved to be native integral
curves. Native existence and uniqueness then give genuine maximal domains,
maximal trajectories, local physical straightness and autonomous time shifts.
Completeness and measure preservation are not assumptions or conclusions.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationAtlasCurves

open LatticeTorus Set Topology Filter TranslationAtlasField
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X]

def timeDomain (e : OpenPartialHomeomorph X Plane) (v : Plane) (x : X) : Set ℝ :=
  {t | e x + t • v ∈ e.target}

def curve (e : OpenPartialHomeomorph X Plane) (v : Plane) (x : X) (t : ℝ) : X :=
  e.symm (e x + t • v)

theorem timeDomain_open (e : OpenPartialHomeomorph X Plane) (v : Plane) (x : X) :
    IsOpen (timeDomain e v x) := e.open_target.preimage (continuous_const.add (continuous_id.smul continuous_const))

theorem zero_mem_timeDomain (e : OpenPartialHomeomorph X Plane) (v : Plane) (x : X) (hx : x ∈ e.source) :
    0 ∈ timeDomain e v x := by
  change e x + (0 : ℝ) • v ∈ e.target
  simpa only [zero_smul, add_zero] using e.map_source hx

theorem curve_zero (e : OpenPartialHomeomorph X Plane) (v : Plane) (x : X) (hx : x ∈ e.source) :
    curve e v x 0 = x := by
  change e.symm (e x + (0 : ℝ) • v) = x
  rw [zero_smul, add_zero]
  exact e.left_inv hx

variable [ChartedSpace Plane X]

def domain (v : Plane) (x : X) : Set ℝ := MaximalIntegralCurve.maximalDomain (TranslationAtlasField.field v) x

def trajectory (v : Plane) (x : X) : ℝ → X := MaximalIntegralCurve.maximalCurve (TranslationAtlasField.field v) x

theorem domain_open (v : Plane) (x : X) : IsOpen (domain v x) := MaximalIntegralCurve.maximalDomain_open _ _

theorem domain_ordConnected (v : Plane) (x : X) : OrdConnected (domain v x) := MaximalIntegralCurve.maximalDomain_ordConnected _ _

theorem domain_convex (v : Plane) (x : X) : Convex ℝ (domain v x) := MaximalIntegralCurve.maximalDomain_convex _ _

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X]

theorem hasMFDerivAt_curve (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) (t : ℝ) (ht : t ∈ timeDomain e v x) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) (curve e v x) t ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  let line := fun s : ℝ => e x + s • v
  have hy : line t ∈ e.target := ht
  have hline : HasDerivAt line v t := by
    simpa [line] using! ((hasDerivAt_id t).smul_const v).const_add (e x)
  have hlineM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) line t ((1 : ℝ →L[ℝ] ℝ).smulRight v) :=
    hline.hasFDerivAt.hasMFDerivAt
  have hinverse := (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, Plane)) he hy).hasMFDerivAt
  rw [mfderiv_atlas_symm_id e he (line t) hy] at hinverse
  have hcomp := hinverse.comp t hlineM
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def, curve, line] using! hcomp

theorem isMIntegralCurveOn_curve (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve e v x) (TranslationAtlasField.field v) (timeDomain e v x) := by
  intro t ht
  rw [TranslationAtlasField.field_eq_const]
  exact (hasMFDerivAt_curve e he v x t ht).hasMFDerivWithinAt

theorem exists_local_integral_curve (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) (hx : x ∈ e.source) :
    ∃ ε > 0, Metric.ball (0 : ℝ) ε ⊆ timeDomain e v x ∧ curve e v x 0 = x ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve e v x) (TranslationAtlasField.field v) (Metric.ball 0 ε) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (timeDomain_open e v x) 0 (zero_mem_timeDomain e v x hx)
  exact ⟨ε, hε, hsub, curve_zero e v x hx, (isMIntegralCurveOn_curve e he v x).mono hsub⟩

theorem zero_mem_domain (v : Plane) (x : X) : 0 ∈ domain v x :=
  MaximalIntegralCurve.zero_mem_maximalDomain (x₀ := x) (TranslationAtlasField.contMDiff_field_one v)

theorem domain_connected (v : Plane) (x : X) : IsConnected (domain v x) :=
  MaximalIntegralCurve.maximalDomain_connected (x₀ := x) (TranslationAtlasField.contMDiff_field_one v)

variable [T2Space X]

theorem trajectory_initial (v : Plane) (x : X) : trajectory v x 0 = x :=
  MaximalIntegralCurve.maximalCurve_initial (x₀ := x) (TranslationAtlasField.contMDiff_field_one v)

theorem trajectory_isMIntegralCurveOn (v : Plane) (x : X) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (trajectory v x) (TranslationAtlasField.field v) (domain v x) :=
  MaximalIntegralCurve.maximalCurve_isMIntegralCurveOn (x₀ := x) (TranslationAtlasField.contMDiff_field_one v)

theorem extends_every_open_interval (v : Plane) (x : X) (U : Set ℝ) (γ : ℝ → X)
    (hU : IsOpen U) (hord : OrdConnected U) (hzero : 0 ∈ U) (hγzero : γ 0 = x)
    (hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) γ (TranslationAtlasField.field v) U) :
    U ⊆ domain v x ∧ EqOn (trajectory v x) γ U :=
  MaximalIntegralCurve.extends_every_open_interval (TranslationAtlasField.contMDiff_field_one v) U γ hU hord hzero hγzero hγ

theorem no_proper_open_interval_extension (v : Plane) (x : X) (U : Set ℝ) (γ : ℝ → X)
    (hU : IsOpen U) (hord : OrdConnected U) (hzero : 0 ∈ U) (hγzero : γ 0 = x)
    (hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) γ (TranslationAtlasField.field v) U) (hcontains : domain v x ⊆ U) :
    U = domain v x ∧ EqOn (trajectory v x) γ U :=
  MaximalIntegralCurve.no_proper_open_interval_extension (TranslationAtlasField.contMDiff_field_one v) U γ hU hord hzero hγzero hγ hcontains

theorem local_representation (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) (hx : x ∈ e.source) :
    ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, t ∈ domain v x ∧ e x + t • v ∈ e.target ∧
      trajectory v x t = curve e v x t := by
  obtain ⟨ε, hε, hsub, hzero, hcurve⟩ := exists_local_integral_curve e he v x hx
  have hmax := extends_every_open_interval v x (Metric.ball 0 ε) (curve e v x) Metric.isOpen_ball
    (convex_ball (0 : ℝ) ε).ordConnected (Metric.mem_ball_self hε) hzero hcurve
  exact ⟨ε, hε, fun t ht => ⟨hmax.1 ht, hsub ht, hmax.2 ht⟩⟩

/-- Every actual chart sees the constructed maximal curve as a physical
straight line on a genuine neighborhood of its initial time. -/
theorem local_physical_straightness (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) (hx : x ∈ e.source) :
    ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, t ∈ domain v x ∧ e (trajectory v x t) = e x + t • v := by
  obtain ⟨ε, hε, hrep⟩ := local_representation e he v x hx
  refine ⟨ε, hε, fun t ht => ?_⟩
  obtain ⟨hD, hline, hcurve⟩ := hrep t ht
  refine ⟨hD, ?_⟩
  rw [hcurve]
  exact e.right_inv hline

theorem domain_at_time (v : Plane) (x : X) (t : ℝ) (ht : t ∈ domain v x) :
    domain v (trajectory v x t) = {s | s + t ∈ domain v x} :=
  MaximalFlowAction.maximalDomain_at_time (TranslationAtlasField.contMDiff_field_one v) x t ht

theorem trajectory_add (v : Plane) (x : X) (t : ℝ) (ht : t ∈ domain v x) (s : ℝ)
    (hs : s ∈ domain v (trajectory v x t)) : trajectory v (trajectory v x t) s = trajectory v x (s + t) :=
  MaximalFlowAction.maximalCurve_add (TranslationAtlasField.contMDiff_field_one v) x t ht s hs

theorem reverse_time (v : Plane) (x : X) (t : ℝ) (ht : t ∈ domain v x) :
    -t ∈ domain v (trajectory v x t) ∧ trajectory v (trajectory v x t) (-t) = x :=
  MaximalFlowAction.reverse_time (TranslationAtlasField.contMDiff_field_one v) x t ht

theorem local_physical_straightness_at_time (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (v : Plane) (x : X) (t : ℝ) (ht : t ∈ domain v x) (hx : trajectory v x t ∈ e.source) :
    ∃ ε > 0, ∀ s ∈ Metric.ball (0 : ℝ) ε, s + t ∈ domain v x ∧
      e (trajectory v x (s + t)) = e (trajectory v x t) + s • v := by
  obtain ⟨ε, hε, hline⟩ := local_physical_straightness e he v (trajectory v x t) hx
  refine ⟨ε, hε, fun s hs => ?_⟩
  obtain ⟨hsD, hsLine⟩ := hline s hs
  have hst : s + t ∈ domain v x := by
    have h := hsD
    rw [domain_at_time v x t ht] at h
    exact h
  exact ⟨hst, (congrArg e (trajectory_add v x t ht s hsD)).symm.trans hsLine⟩

end MNEC.TranslationAtlasCurves

