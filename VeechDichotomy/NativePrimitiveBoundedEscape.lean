module

public import MNEC.NativePrimitiveTrajectory
public import MNEC.NativeCompleteDirectionalFlow
public import VeechDichotomy.NativePrimitiveRectangles
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen

/-! A bounded primitive forces a complete native vertical trajectory
to leave its domain in bounded time, even when the primitive has zeros
and is not injective. The actual trajectory reaches the domain frontier.
This is the local mechanism for escaping limiting zero neighborhoods. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePrimitiveBoundedEscape

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow MNEC.NativePrimitiveTrajectory
open NativePrimitiveRectangles Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem affinity_on_preconnected (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (I : Set ℝ) (hI : IsPreconnected I) (hD : I ⊆ domain q v x)
    (hstay : ∀ t ∈ I, (trajectory q v x t).val ∈ U) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    value q v x F t = value q v x F s + (t - s) • v := by
  let H : I → Plane := fun u => value q v x F u.val - u.val • v
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  have hlocal : IsLocallyConstant H := by
    apply (IsLocallyConstant.iff_eventually_eq H).mpr
    intro u
    have hg := affinity_germ q v x U hU F hF u.val (hD u.property) (hstay u.val u.property)
    have hc : Tendsto (Subtype.val : I → ℝ) (𝓝 u) (𝓝 u.val) := continuous_subtype_val.continuousAt.tendsto
    filter_upwards [hc hg] with z hz
    dsimp only [H]
    rw [hz, sub_smul]
    abel
  have heq := hlocal.apply_eq_of_preconnectedSpace (⟨t, ht⟩ : I) (⟨s, hs⟩ : I)
  change value q v x F t - t • v = value q v x F s - s • v at heq
  rw [sub_smul]
  calc
    value q v x F t = (value q v x F t - t • v) + t • v := by abel
    _ = (value q v x F s - s • v) + t • v := by rw [heq]
    _ = value q v x F s + (t • v - s • v) := by abel

theorem exits (x : CompleteOrbits q vertical) (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (M : ℝ) (hbound : ∀ y ∈ U, |(F y).im| ≤ M) (hx : x.val.val ∈ U) :
    ∃ s ∈ Icc 0 (2 * M + 1), (trajectory q vertical x.val s).val ∉ U := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound x.val.val hx)
  by_contra hnone
  push Not at hnone
  have hstay : ∀ s ∈ Icc 0 (2 * M + 1), (trajectory q vertical x.val s).val ∈ U := hnone
  have hT : (0 : ℝ) ≤ 2 * M + 1 := by linarith
  have heq := affinity_on_preconnected q vertical x.val U hU F hF (Icc 0 (2 * M + 1))
    isPreconnected_Icc (fun s _ => complete_time_mem q vertical x s) hstay ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
  have him := congrArg Prod.snd heq
  change (F (trajectory q vertical x.val (2 * M + 1)).val).im =
    (F (trajectory q vertical x.val 0).val).im + ((2 * M + 1) - 0) * 1 at him
  rw [trajectory_initial] at him
  have h0 := abs_le.mp (hbound x.val.val hx)
  have h1 := abs_le.mp (hbound _ (hstay _ ⟨hT, le_rfl⟩))
  linarith

theorem crosses_frontier {Ω : Type*} [TopologicalSpace Ω] (f : ℝ → Ω) (hf : Continuous f)
    (U : Set Ω) (hU : IsOpen U) {T : ℝ} (hT : 0 ≤ T) (h0 : f 0 ∈ U) (h1 : f T ∉ U) :
    ∃ s ∈ Icc 0 T, f s ∈ frontier U := by
  by_contra hnone
  push Not at hnone
  let g : Icc (0 : ℝ) T → Ω := fun s => f s.val
  have hg : Continuous g := hf.comp continuous_subtype_val
  have heq : g ⁻¹' U = g ⁻¹' closure U := by
    ext s
    change f s.val ∈ U ↔ f s.val ∈ closure U
    refine ⟨fun hs => subset_closure hs, ?_⟩
    intro hs
    rw [closure_eq_self_union_frontier] at hs
    exact hs.resolve_right (hnone s.val s.property)
  have hclosed : IsClosed (g ⁻¹' U) := by
    rw [heq]
    exact isClosed_closure.preimage hg
  let : PreconnectedSpace (Icc (0 : ℝ) T) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hclopen : IsClopen (g ⁻¹' U) := ⟨hclosed, hU.preimage hg⟩
  have huniv : g ⁻¹' U = univ := hclopen.eq_univ ⟨⟨0, le_rfl, hT⟩, h0⟩
  have hmem : (⟨T, hT, le_rfl⟩ : Icc (0 : ℝ) T) ∈ g ⁻¹' U := huniv.symm ▸ mem_univ _
  exact h1 hmem

theorem reaches_frontier (x : CompleteOrbits q vertical) (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (M : ℝ) (hbound : ∀ y ∈ U, |(F y).im| ≤ M) (hx : x.val.val ∈ U) :
    ∃ s ∈ Icc 0 (2 * M + 1), (trajectory q vertical x.val s).val ∈ frontier U := by
  obtain ⟨T, hT, hexit⟩ := exits q x U hU F hF M hbound hx
  have hc : Continuous (fun s : ℝ => (flow q vertical s x).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      ((continuous_joint_timeMap q vertical).comp (continuous_id.prodMk continuous_const)))
  have h0 : (flow q vertical 0 x).val.val ∈ U := by simpa only [Flow.map_zero_apply] using hx
  obtain ⟨s, hs, hfront⟩ := crosses_frontier (fun s => (flow q vertical s x).val.val) hc U hU hT.1 h0 hexit
  exact ⟨s, ⟨hs.1, hs.2.trans hT.2⟩, hfront⟩

end VeechDichotomy.NativePrimitiveBoundedEscape
