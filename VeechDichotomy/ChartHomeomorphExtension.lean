module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.Separation.Regular

/-! Extend actual plane homeomorphisms supported in a compact part of
a chart target to whole-surface homeomorphisms. Joint continuity of both
directions is proved from the chart formula and identity off the support.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ChartHomeomorphExtension

open Set Filter Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

def value (e : OpenPartialHomeomorph X ℂ) (H : ℂ ≃ₜ ℂ) (x : X) : X :=
  if x ∈ e.source then e.symm (H (e x)) else x

theorem value_mem_source (e : OpenPartialHomeomorph X ℂ) (H : ℂ ≃ₜ ℂ)
    (hT : MapsTo H e.target e.target) {x : X} (hx : x ∈ e.source) : value e H x ∈ e.source := by
  rw [value, ite_eq_left hx]
  exact e.map_target (hT (e.map_source hx))

theorem inverse_value (e : OpenPartialHomeomorph X ℂ) (H : ℂ ≃ₜ ℂ)
    (hT : MapsTo H e.target e.target) (x : X) :
    value e H.symm (value e H x) = x := by
  by_cases hx : x ∈ e.source
  · rw [value, ite_eq_left (value_mem_source e H hT hx), value, ite_eq_left hx,
      e.right_inv (hT (e.map_source hx)), Homeomorph.symm_apply_apply, e.left_inv hx]
  · have hv : value e H x = x := by rw [value, ite_eq_right hx]
    rw [hv, value, ite_eq_right hx]

def support (e : OpenPartialHomeomorph X ℂ) (K : Set ℂ) : Set X := e.symm '' K

theorem support_compact (e : OpenPartialHomeomorph X ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKe : K ⊆ e.target) : IsCompact (support e K) :=
  hK.image_of_continuousOn (e.symm.continuousOn.mono hKe)

theorem support_subset_source (e : OpenPartialHomeomorph X ℂ) {K : Set ℂ}
    (hKe : K ⊆ e.target) : support e K ⊆ e.source := by
  rintro _ ⟨z, hz, rfl⟩
  exact e.map_target (hKe hz)

theorem inverse_fixed (H : ℂ ≃ₜ ℂ) {K : Set ℂ} (hfix : ∀ z ∉ K, H z = z)
    {z : ℂ} (hz : z ∉ K) : H.symm z = z := by
  have h := H.symm_apply_apply z
  rwa [hfix z hz] at h

theorem value_fixed (e : OpenPartialHomeomorph X ℂ) (H : ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hfix : ∀ z ∉ K, H z = z) {x : X} (hx : x ∉ support e K) : value e H x = x := by
  by_cases he : x ∈ e.source
  · have hc : e x ∉ K := fun h => hx ⟨e x, h, e.left_inv he⟩
    rw [value, ite_eq_left he, hfix _ hc, e.left_inv he]
  · rw [value, ite_eq_right he]

variable {P : Type*} [TopologicalSpace P] [T2Space X]

theorem continuous_value (e : OpenPartialHomeomorph X ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKe : K ⊆ e.target) (F : P → ℂ ≃ₜ ℂ)
    (hT : ∀ p, MapsTo (F p) e.target e.target)
    (hfix : ∀ p z, z ∉ K → F p z = z)
    (hF : Continuous (fun p : P × ℂ => F p.1 p.2)) :
    Continuous (fun p : P × X => value e (F p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hx : p.2 ∈ e.source
  · have hcoord : ContinuousAt (fun q : P × X => e q.2) p :=
      ContinuousAt.comp (f := Prod.snd) (e.continuousAt hx) continuousAt_snd
    have hplane : ContinuousAt (fun q : P × X => F q.1 (e q.2)) p :=
      ContinuousAt.comp (f := fun q : P × X => (q.1, e q.2)) hF.continuousAt
        (continuousAt_fst.prodMk hcoord)
    have hlocal : ContinuousAt (fun q : P × X => e.symm (F q.1 (e q.2))) p :=
      ContinuousAt.comp (f := fun q : P × X => F q.1 (e q.2))
        (e.symm.continuousAt (hT p.1 (e.map_source hx))) hplane
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt (e.open_source.mem_nhds hx)] with q hq
    change q.2 ∈ e.source at hq
    rw [value, ite_eq_left hq]
  · have hnot : p.2 ∉ support e K := fun h => hx (support_subset_source e hKe h)
    have hnear : ∀ᶠ q : P × X in 𝓝 p, q.2 ∉ support e K :=
      continuous_snd.continuousAt ((support_compact e hK hKe).isClosed.isOpen_compl.mem_nhds hnot)
    apply continuousAt_snd.congr_of_eventuallyEq
    filter_upwards [hnear] with q hq
    exact value_fixed e (F q.1) (hfix q.1) hq

def homeomorph (e : OpenPartialHomeomorph X ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKe : K ⊆ e.target) (F : P → ℂ ≃ₜ ℂ)
    (hT : ∀ p, MapsTo (F p) e.target e.target)
    (hI : ∀ p, MapsTo (F p).symm e.target e.target)
    (hfix : ∀ p z, z ∉ K → F p z = z)
    (hF : Continuous (fun p : P × ℂ => F p.1 p.2))
    (hInv : Continuous (fun p : P × ℂ => (F p.1).symm p.2)) (p : P) : X ≃ₜ X where
  toFun := value e (F p)
  invFun := value e (F p).symm
  left_inv := inverse_value e (F p) (hT p)
  right_inv := inverse_value e (F p).symm (hI p)
  continuous_toFun := (continuous_value e hK hKe F hT hfix hF).comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_value e hK hKe (fun p => (F p).symm) hI
    (fun p _ hz => inverse_fixed (F p) (hfix p) hz) hInv).comp
      (continuous_const.prodMk continuous_id)

end VeechDichotomy.ChartHomeomorphExtension
