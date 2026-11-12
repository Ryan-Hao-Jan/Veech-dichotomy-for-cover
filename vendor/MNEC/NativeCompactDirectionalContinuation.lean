module

public import MNEC.NativePartialDirectionalFlow
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Choose

/-!
# Actual compact regular continuation of an arbitrary native differential

Joint openness of the proved native valid-time domain supplies a local
uniform time interval. A finite subcover then supplies uniform continuation
on each compact regular set. No completeness assumption is used.
-/

noncomputable section
@[expose] public section

namespace MNEC.NativeCompactDirectionalContinuation

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics Set Topology
open scoped Classical Topology Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : NativeAbelianDifferential.Differential X)
local notation "R" => Regular q

theorem local_uniform_continuation (v : Plane) (x : R) :
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ U, Icc (-ε) ε ⊆ domain q v y := by
  let V : Set (ℝ × R) := {p | p.1 ∈ domain q v p.2}
  have hV : IsOpen V := (NativePartialDirectionalFlow.valid_open q).preimage
    (continuous_const.prodMk continuous_id)
  have hxV : ((0 : ℝ), x) ∈ V := zero_mem_domain q v x
  obtain ⟨T, U, hT, hU, hzeroT, hxU, hTU⟩ := isOpen_prod_iff.mp hV 0 x hxV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hT 0 hzeroT
  refine ⟨U, hU, hxU, r / 2, by linarith, ?_⟩
  intro y hy t ht
  have htball : t ∈ Metric.ball (0 : ℝ) r := by
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith only [ht.1, ht.2, hr]
  have hp : (t, y) ∈ T ×ˢ U := ⟨hball htball, hy⟩
  exact hTU hp

theorem uniform_continuation_on_compact (v : Plane) (K : Set R) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, Icc (-ε) ε ⊆ domain q v x := by
  choose U hU hcenter ε hε hstep using local_uniform_continuation q v
  obtain ⟨F, hcover⟩ := hK.elim_finite_subcover U hU
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hcenter x⟩)
  by_cases hF : F.Nonempty
  · let ε₀ := F.inf' hF ε
    have hε₀ : 0 < ε₀ := (Finset.lt_inf'_iff hF).mpr (fun x _ => hε x)
    refine ⟨ε₀, hε₀, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨hiF, hxi⟩ := Set.mem_iUnion.mp hi
    have hle : ε₀ ≤ ε i := Finset.inf'_le ε hiF
    exact (Icc_subset_Icc (neg_le_neg hle) hle).trans (hstep i x hxi)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have h := hcover hx
    have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hempty] at h

/-- A native orbit cannot stay in a compact regular set arbitrarily
close to ANY excluded finite time: actual uniform continuation and the
proved native time-shift formula would put that time in its domain. -/
theorem avoids_compact_near_excluded_time (v : Plane) (x : R) (B : ℝ)
    (hB : B ∉ domain q v x) (K : Set R) (hK : IsCompact K) :
    ∃ ε > 0, ∀ t ∈ domain q v x, |B - t| ≤ ε → trajectory q v x t ∉ K := by
  obtain ⟨ε, hε, hstep⟩ := uniform_continuation_on_compact q v K hK
  refine ⟨ε, hε, fun t ht hnear hmem => ?_⟩
  have htime : B - t ∈ domain q v (trajectory q v x t) := hstep _ hmem (abs_le.mp hnear)
  rw [domain_at_time q v x t ht] at htime
  apply hB
  simpa only [mem_ofPred_eq, sub_add_cancel] using htime

theorem eventually_avoids_compact (v : Plane) (x : R) (B : ℝ)
    (hB : B ∉ domain q v x) (K : Set R) (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[domain q v x] B, trajectory q v x t ∉ K := by
  obtain ⟨ε, hε, havoid⟩ := avoids_compact_near_excluded_time q v x B hB K hK
  have hball : ∀ᶠ t in 𝓝 B, t ∈ Metric.ball B ε := Metric.ball_mem_nhds B hε
  have hnear : ∀ᶠ t in 𝓝[domain q v x] B, t ∈ Metric.ball B ε :=
    hball.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with t ht hball
  apply havoid t ht
  have hdist : |t - B| < ε := by simpa only [Metric.mem_ball, Real.dist_eq] using hball
  rw [abs_sub_comm]
  exact hdist.le

theorem compact_regular_lift (K : Set X) (hK : IsCompact K) (hreg : K ⊆ NativeAbelianDifferential.regularSet q) :
    IsCompact ((Subtype.val : R → X) ⁻¹' K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → R := fun x => ⟨x.val, hreg x.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have himage : f '' (univ : Set K) = (Subtype.val : R → X) ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, mem_univ _, Subtype.ext rfl⟩
  rw [← himage]
  exact isCompact_univ.image hf

theorem eventually_avoids_original_compact (v : Plane) (x : R) (B : ℝ)
    (hB : B ∉ domain q v x) (K : Set X) (hK : IsCompact K)
    (hreg : K ⊆ NativeAbelianDifferential.regularSet q) :
    ∀ᶠ t in 𝓝[domain q v x] B, (trajectory q v x t).val ∉ K :=
  eventually_avoids_compact q v x B hB ((Subtype.val : R → X) ⁻¹' K) (compact_regular_lift q K hK hreg)

/-- Near a missing finite endpoint the observed native trajectory enters
EVERY original open neighborhood of the actual zero set. This follows
from actual regular continuation and original compactness, not an escape
or endpoint hypothesis supplied by the user. -/
theorem eventually_near_zeros (v : Plane) (x : R) (B : ℝ) (hB : B ∉ domain q v x)
    (U : Set X) (hU : IsOpen U) (hzeros : NativeAbelianDifferential.zeroSet q ⊆ U) :
    ∀ᶠ t in 𝓝[domain q v x] B, (trajectory q v x t).val ∈ U := by
  have hreg : Uᶜ ⊆ NativeAbelianDifferential.regularSet q := by
    intro y hy hzero
    exact hy (hzeros hzero)
  have h := eventually_avoids_original_compact q v x B hB Uᶜ hU.isClosed_compl.isCompact hreg
  filter_upwards [h] with t ht
  exact not_not.mp ht

end MNEC.NativeCompactDirectionalContinuation



