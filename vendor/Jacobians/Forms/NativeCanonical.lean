module

/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

Minimal native analytic zero-divisor core, extracted from pinned upstream
73212f7ef2bb46a7884710b18fe1e18b8509e3e5; extraction/Lean4.35 port2026-10-31.
Source declarations: ResidueCalculus/FormCoeff, ResidueTheorem/OmegaFactorization,
Cech/MeromorphicAnalyticBadSet, TailDuality/TailDualityInjective.
Only the namespace and definitionally identical divisor type are changed.
This does not assume degree2g-2 or import the unverified RR/duality engine.
-/
public import Jacobians.Forms.HolomorphicForms
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.LocallyFinsupp

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Filter Metric Set

set_option backward.isDefEq.respectTransparency false

namespace Jacobians.NativeCanonical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem finite_of_forall_eventually_nhdsNE_notMem {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] {S : Set Y} (h : ∀ x : Y, ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Finite := by
  have hloc : LocallyFiniteSupport (S.indicator (fun _ => (1 : ℕ))) := by
    intro z
    have hz := h z
    rw [eventually_nhdsWithin_iff, _root_.eventually_nhds_iff] at hz
    obtain ⟨t, ht, htopen, hzt⟩ := hz
    refine ⟨t, htopen.mem_nhds hzt, (Set.finite_singleton z).subset ?_⟩
    rintro y ⟨hyt, hysupp⟩
    by_contra hne
    have hyS : y ∈ S := by
      by_contra hyS
      exact hysupp (Set.indicator_of_notMem hyS _)
    exact ht y hyt (by simpa using hne) hyS
  have hfin := hloc.finite_inter_support_of_isCompact (isCompact_univ (X := Y))
  rw [Set.univ_inter] at hfin
  refine hfin.subset fun y hy => ?_
  rw [Function.mem_support, Set.indicator_of_mem hy]
  exact one_ne_zero

noncomputable def coeffAt (α : HolomorphicOneForms X) (a : X) : ℂ → ℂ :=
  fun z => Jacobians.Montel.localRep α a ((chartAt ℂ a).symm z)

/-- `coeffAt α a` is analytic on the chart target (reuse of the Montel analyticity bridge). -/
theorem coeffAt_analyticOn (α : HolomorphicOneForms X) (a : X) :
    AnalyticOn ℂ (coeffAt α a) (chartAt ℂ a).target :=
  Jacobians.Montel.localRep_analyticOn_chartTarget α a

/-- `coeffAt α a` is analytic at the chart image of any point of the chart source. -/
theorem coeffAt_analyticAt (α : HolomorphicOneForms X) (a : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    AnalyticAt ℂ (coeffAt α a) z :=
  (coeffAt_analyticOn α a).analyticAt ((chartAt ℂ a).open_target.mem_nhds hz)

theorem tendsto_chart_nhdsNE {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    Tendsto (chartAt (H := ℂ) x) (𝓝[≠] x) (𝓝[≠] ((chartAt (H := ℂ) x) x)) := by
  have hx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((chartAt (H := ℂ) x).continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hx)] with y hy hysrc
  exact fun heq => hy ((chartAt (H := ℂ) x).injOn hysrc hx heq)

theorem localRep_eq_zero_of_toFun_eq_zero (α : HolomorphicOneForms X) (x₀ : X) {y : X}
    (h : α.toFun y = 0) : Jacobians.Montel.localRep α x₀ y = 0 := by
  unfold Jacobians.Montel.localRep
  rw [h]
  exact zero_apply _

/-- Conversely, on the chart source a vanishing local representative kills the 1-form value: the
transported unit tangent spans the 1-dimensional fibre (off-centre generalization of the
`exists_localRep_self_ne_zero` argument). -/
theorem toFun_eq_zero_of_localRep_eq_zero (α : HolomorphicOneForms X) {x₀ y : X}
    (hy : y ∈ (chartAt (H := ℂ) x₀).source)
    (h : Jacobians.Montel.localRep α x₀ y = 0) : α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with he
  have hybase : y ∈ e.baseSet := hy
  refine ContinuousLinearMap.ext fun v => ?_
  rw [zero_apply]
  have hv : e.symmL ℂ y (e.continuousLinearMapAt ℂ y v) = v :=
    e.symmL_continuousLinearMapAt hybase v
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ)
    rwa [smul_eq_mul, mul_one] at h2
  calc α.toFun y v = α.toFun y (e.symmL ℂ y c) := by rw [hv]
    _ = α.toFun y (c • e.symmL ℂ y 1) := by rw [hsm]
    _ = c • α.toFun y (e.symmL ℂ y 1) := by rw [(α.toFun y).map_smul]
    _ = c • Jacobians.Montel.localRep α x₀ y := rfl
    _ = 0 := by rw [h, smul_zero]

/-- Chart-side eventual vanishing of the coefficient pushes to manifold-side eventual vanishing
of the 1-form (the fibres are 1-dimensional, spanned by the chart tangent). -/
theorem toFun_eventually_zero_of_coeffAt_eventually_zero (α : HolomorphicOneForms X) {p : X}
    (h : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) p) p), coeffAt α p w = 0) :
    ∀ᶠ y in 𝓝 p, α.toFun y = 0 := by
  have hp : p ∈ (chartAt (H := ℂ) p).source := mem_chart_source ℂ p
  have hcont : ContinuousAt (chartAt (H := ℂ) p) p := (chartAt (H := ℂ) p).continuousAt hp
  filter_upwards [hcont.eventually h,
    (chartAt (H := ℂ) p).open_source.mem_nhds hp] with y hy hysrc
  have hcoeff : coeffAt α p ((chartAt (H := ℂ) p) y) = Jacobians.Montel.localRep α p y := by
    simp only [coeffAt]
    rw [(chartAt (H := ℂ) p).left_inv hysrc]
  rw [hcoeff] at hy
  exact toFun_eq_zero_of_localRep_eq_zero α hysrc hy

/-- **Identity theorem for holomorphic 1-forms (global propagation).**  If the canonical-chart
coefficient of `α` vanishes on a neighbourhood of one chart centre, then `α = 0` — the set where
`α` vanishes locally is clopen (openness is trivial; closedness is the one-variable isolated-zeros
dichotomy applied to the analytic coefficient), and `X` is connected. -/
theorem eq_zero_of_coeffAt_eventually_zero (α : HolomorphicOneForms X) {x : X}
    (h : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) x) x), coeffAt α x w = 0) : α = 0 := by
  classical
  set S := {p : X | ∀ᶠ y in 𝓝 p, α.toFun y = 0} with hSdef
  have hopen : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    -- the coefficient at `p` is not eventually zero (else `p ∈ S`) …
    have hno : ¬ ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) p) p), coeffAt α p w = 0 := fun hev =>
      hp (toFun_eventually_zero_of_coeffAt_eventually_zero α hev)
    have hpt : (chartAt (H := ℂ) p) p ∈ (chartAt (H := ℂ) p).target :=
      (chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p)
    -- … so by the isolated-zeros dichotomy it is eventually NONZERO on the punctured chart nbhd
    have hne : ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) p) p), coeffAt α p w ≠ 0 :=
      ((coeffAt_analyticAt α p hpt).eventually_eq_zero_or_eventually_ne_zero).resolve_left hno
    -- transfer to `X`: punctured-near `p`, the form does not vanish, so no point lies in `S`
    have h1 := (tendsto_chart_nhdsNE p).eventually hne
    have h2 : ∀ᶠ y in 𝓝[≠] p, y ∈ (chartAt (H := ℂ) p).source :=
      eventually_nhdsWithin_of_eventually_nhds
        ((chartAt (H := ℂ) p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hXne : ∀ᶠ y in 𝓝[≠] p, y ∈ Sᶜ := by
      filter_upwards [h1, h2] with y hy hysrc
      intro hyS
      apply hy
      have hzero : α.toFun y = 0 :=
        (show ∀ᶠ z in 𝓝 y, α.toFun z = 0 from hyS).self_of_nhds
      show coeffAt α p ((chartAt (H := ℂ) p) y) = 0
      simp only [coeffAt]
      rw [(chartAt (H := ℂ) p).left_inv hysrc]
      exact localRep_eq_zero_of_toFun_eq_zero α p hzero
    rw [eventually_nhdsWithin_iff] at hXne
    rw [← Filter.eventually_mem_set]
    filter_upwards [hXne] with y hy
    by_cases hyp : y = p
    · subst hyp; exact hp
    · exact hy (by simpa using hyp)
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with hempty | huniv
  · exfalso
    have hxS : x ∈ S := toFun_eventually_zero_of_coeffAt_eventually_zero α h
    rw [hempty] at hxS
    exact hxS
  · refine ContMDiffSection.ext fun y => ?_
    have hyS : y ∈ S := by rw [huniv]; trivial
    exact (show ∀ᶠ z in 𝓝 y, α.toFun z = 0 from hyS).self_of_nhds

/-- **Isolated zeros of a nonzero holomorphic 1-form**: at every chart centre, the canonical-chart
coefficient is eventually nonzero on the punctured neighbourhood. -/
theorem coeffAt_eventually_ne_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) (x : X) :
    ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) x) x), coeffAt α x w ≠ 0 := by
  have hpt : (chartAt (H := ℂ) x) x ∈ (chartAt (H := ℂ) x).target :=
    (chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x)
  refine ((coeffAt_analyticAt α x hpt).eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
  exact fun hz => hα (eq_zero_of_coeffAt_eventually_zero α hz)

/-- **The zero set of a nonzero holomorphic 1-form is FINITE** (the `div(ω₀) ≥ 0` finiteness atom:
zeros are isolated by `coeffAt_eventually_ne_zero` + the chart-transition comparison, and `X` is
compact). -/
theorem finite_localRep_self_eq_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    {x : X | Jacobians.Montel.localRep α x x = 0}.Finite := by
  refine finite_of_forall_eventually_nhdsNE_notMem fun x => ?_
  have h1 := (tendsto_chart_nhdsNE x).eventually (coeffAt_eventually_ne_zero α hα x)
  have h2 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt (H := ℂ) x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt (H := ℂ) x).open_source.mem_nhds (mem_chart_source ℂ x))
  filter_upwards [h1, h2] with y hy hysrc
  intro hzero
  -- the coefficient in `x`'s chart is nonzero at `y` …
  have hxy : Jacobians.Montel.localRep α x y ≠ 0 := by
    have hcoeff : coeffAt α x ((chartAt (H := ℂ) x) y) = Jacobians.Montel.localRep α x y := by
      simp only [coeffAt]
      rw [(chartAt (H := ℂ) x).left_inv hysrc]
    rwa [hcoeff] at hy
  -- … and differs from the own-chart coefficient by the nonzero transition factor
  have htrans := Jacobians.Montel.localRep_chart_transition α x y y (mem_chart_source ℂ y) hysrc
  rw [hzero] at htrans
  rcases mul_eq_zero.mp htrans.symm with hc | hl
  · exact Jacobians.Montel.chartTransitionFactor_ne_zero (X := X) x y y hc
  · exact hxy hl

theorem analyticAt_coeffAt_self (ω₀ : HolomorphicOneForms X) (p : X) :
    AnalyticAt ℂ (fun z => coeffAt ω₀ p z) ((chartAt (H := ℂ) p) p) :=
  coeffAt_analyticAt ω₀ p ((chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p))

noncomputable def omegaOrderAt (ω₀ : HolomorphicOneForms X) (p : X) : WithTop ℤ :=
  meromorphicOrderAt (fun z => coeffAt ω₀ p z) ((chartAt (H := ℂ) p) p)

/-- For `ω₀ ≠ 0`, the order is finite at every point (the coefficient is not eventually zero —
the identity-theorem atom `coeffAt_eventually_ne_zero`). -/
theorem omegaOrderAt_ne_top (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    omegaOrderAt ω₀ p ≠ ⊤ := by
  rw [omegaOrderAt, Ne, meromorphicOrderAt_eq_top_iff]
  intro hev
  obtain ⟨z, hz0, hzne⟩ := (hev.and (coeffAt_eventually_ne_zero ω₀ hω₀ p)).exists
  exact hzne hz0

/-- The chart-centre value of `coeffAt` is `localRep` on the diagonal. -/
theorem coeffAt_self_eq_localRep (ω₀ : HolomorphicOneForms X) (p : X) :
    coeffAt ω₀ p ((chartAt (H := ℂ) p) p) = Jacobians.Montel.localRep ω₀ p p := by
  rw [coeffAt, (chartAt (H := ℂ) p).left_inv (mem_chart_source ℂ p)]

/-- A nonzero chart-centre value forces order `0` (continuity + the order-zero criterion). -/
theorem omegaOrderAt_eq_zero_of_localRep_ne_zero (ω₀ : HolomorphicOneForms X) (p : X)
    (hval : Jacobians.Montel.localRep ω₀ p p ≠ 0) :
    omegaOrderAt ω₀ p = 0 := by
  rw [omegaOrderAt, ← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (analyticAt_coeffAt_self ω₀ p).meromorphicAt]
  refine ⟨Jacobians.Montel.localRep ω₀ p p, hval, ?_⟩
  rw [← coeffAt_self_eq_localRep ω₀ p]
  exact ((analyticAt_coeffAt_self ω₀ p).continuousAt.tendsto).mono_left nhdsWithin_le_nhds

/-- **The canonical divisor `K = div ω₀`** (Miranda p. 191; Forster 17.4): the zero divisor of a
nonzero holomorphic 1-form, supported on its finite zero set. -/
noncomputable def canonicalDivisorOf (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) : X →₀ ℤ :=
  Finsupp.onFinset (finite_localRep_self_eq_zero ω₀ hω₀).toFinset
    (fun p => WithTop.untopD 0 (omegaOrderAt ω₀ p))
    (fun p hne => by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      by_contra hval
      apply hne
      show WithTop.untopD 0 (omegaOrderAt ω₀ p) = 0
      rw [omegaOrderAt_eq_zero_of_localRep_ne_zero ω₀ p hval]
      rfl)

theorem canonicalDivisorOf_apply (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    canonicalDivisorOf ω₀ hω₀ p = WithTop.untopD 0 (omegaOrderAt ω₀ p) := rfl

/-- The canonical divisor reads the order: `(K p : WithTop ℤ) = omegaOrderAt ω₀ p`. -/
theorem coe_canonicalDivisorOf (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    ((canonicalDivisorOf ω₀ hω₀ p : ℤ) : WithTop ℤ) = omegaOrderAt ω₀ p := by
  rw [canonicalDivisorOf_apply]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (omegaOrderAt_ne_top ω₀ hω₀ p)
  rw [← hk]
  rfl

end Jacobians.NativeCanonical
