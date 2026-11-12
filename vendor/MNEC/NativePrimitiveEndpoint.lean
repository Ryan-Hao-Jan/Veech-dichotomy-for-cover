module

public import MNEC.NativePrimitiveTrajectory
public import MNEC.NativePrimitiveLineNull

@[expose] public section
noncomputable section

namespace MNEC.NativePrimitiveEndpoint

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics
open NativePrimitiveTrajectory NativePrimitiveLineNull NativeRegularArea MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Classical

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- A genuine finite observed endpoint determines the exact primitive
value on the entire connected tail. The affinity is proved, not supplied. -/
theorem value_of_endpoint_limit (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I) (hD : I ⊆ domain q v x)
    (hstay : ∀ t ∈ I, (trajectory q v x t).val ∈ U)
    (B : ℝ) [NeBot (𝓝[I] B)] (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[I] B) (𝓝 b₀))
    (s : ℝ) (hs : s ∈ I) : value q v x F s = (s - B) • v := by
  have hcont : ContinuousAt (fun y : X => toPlane (F y)) b₀ :=
    toPlane.continuous.continuousAt.comp (hF b₀ hb₀).mdifferentiableAt.continuousAt
  have hzero : Tendsto (value q v x F) (𝓝[I] B) (𝓝 (0 : Plane)) := by
    change Tendsto (fun t : ℝ => toPlane (F (trajectory q v x t).val)) (𝓝[I] B) (𝓝 (0 : Plane))
    simpa only [Function.comp_def, hFb₀, map_zero] using hcont.tendsto.comp hlim
  have heq : value q v x F =ᶠ[𝓝[I] B] fun t => value q v x F s + (t - s) • v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact affinity_on_open_convex q v x U hU F hF I hI hconvex hD hstay s t hs ht
  have haffine : Continuous (fun t : ℝ => value q v x F s + (t - s) • v) :=
    continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  have hlimAffine : Tendsto (value q v x F) (𝓝[I] B)
      (𝓝 (value q v x F s + (B - s) • v)) :=
    (haffine.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have hval : value q v x F s + (B - s) • v = 0 := tendsto_nhds_unique hlimAffine hzero
  have h := congrArg (fun p : Plane => p - (B - s) • v) hval
  simpa only [add_sub_cancel_right, zero_sub, ← neg_smul, neg_sub] using h

theorem endpoint_tail_in_linePreimage (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I) (hD : I ⊆ domain q v x)
    (hstay : ∀ t ∈ I, (trajectory q v x t).val ∈ U)
    (B : ℝ) [NeBot (𝓝[I] B)] (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[I] B) (𝓝 b₀)) :
    ∀ s ∈ I, trajectory q v x s ∈ linePreimage q U F 0 v := by
  intro s hs
  refine ⟨hstay s hs, ?_⟩
  change value q v x F s ∈ affineLine 0 v
  rw [value_of_endpoint_limit q v x U hU F hF I hI hconvex hD hstay B b₀ hb₀ hFb₀ hlim s hs]
  change ((s - B) * v.1 - 0) * v.2 - ((s - B) * v.2 - 0) * v.1 = 0
  ring

/-- Concrete terminal interval: its nontrivial endpoint filter is derived
from A<B. This is ready for a genuine finite forward maximal endpoint. -/
theorem forward_endpoint_tail_in_linePreimage (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (A B : ℝ) (hAB : A < B) (hD : Ioo A B ⊆ domain q v x)
    (hstay : ∀ t ∈ Ioo A B, (trajectory q v x t).val ∈ U)
    (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[<] B) (𝓝 b₀)) :
    ∀ s ∈ Ioo A B, trajectory q v x s ∈ linePreimage q U F 0 v := by
  let : NeBot (𝓝[Ioo A B] B) := right_nhdsWithin_Ioo_neBot hAB
  apply endpoint_tail_in_linePreimage q v x U hU F hF (Ioo A B) isOpen_Ioo (convex_Ioo A B)
    hD hstay B b₀ hb₀ hFb₀
  simpa only [nhdsWithin_Ioo_eq_nhdsLT hAB] using hlim

/-- The same actual tail is contained in a canonical area-null set for
every nonzero physical velocity. No critical-ray nullness premise is used. -/
theorem forward_endpoint_tail_in_null_set (q : Differential X) (v : Plane) (hv : v ≠ 0) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (A B : ℝ) (hAB : A < B) (hD : Ioo A B ⊆ domain q v x)
    (hstay : ∀ t ∈ Ioo A B, (trajectory q v x t).val ∈ U)
    (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[<] B) (𝓝 b₀)) :
    regularArea q (linePreimage q U F 0 v) = 0 ∧
      ∀ s ∈ Ioo A B, trajectory q v x s ∈ linePreimage q U F 0 v :=
  ⟨linePreimage_null q U hU F hF 0 v hv,
    forward_endpoint_tail_in_linePreimage q v x U hU F hF A B hAB hD hstay b₀ hb₀ hFb₀ hlim⟩

theorem backward_endpoint_tail_in_linePreimage (q : Differential X) (v : Plane) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (A B : ℝ) (hAB : A < B) (hD : Ioo A B ⊆ domain q v x)
    (hstay : ∀ t ∈ Ioo A B, (trajectory q v x t).val ∈ U)
    (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[>] A) (𝓝 b₀)) :
    ∀ s ∈ Ioo A B, trajectory q v x s ∈ linePreimage q U F 0 v := by
  let : NeBot (𝓝[Ioo A B] A) := left_nhdsWithin_Ioo_neBot hAB
  apply endpoint_tail_in_linePreimage q v x U hU F hF (Ioo A B) isOpen_Ioo (convex_Ioo A B)
    hD hstay A b₀ hb₀ hFb₀
  simpa only [nhdsWithin_Ioo_eq_nhdsGT hAB] using hlim

theorem backward_endpoint_tail_in_null_set (q : Differential X) (v : Plane) (hv : v ≠ 0) (x : Regular q)
    (U : Set X) (hU : IsOpen U) (F : X → ℂ)
    (hF : ∀ y ∈ U, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y))
    (A B : ℝ) (hAB : A < B) (hD : Ioo A B ⊆ domain q v x)
    (hstay : ∀ t ∈ Ioo A B, (trajectory q v x t).val ∈ U)
    (b₀ : X) (hb₀ : b₀ ∈ U) (hFb₀ : F b₀ = 0)
    (hlim : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[>] A) (𝓝 b₀)) :
    regularArea q (linePreimage q U F 0 v) = 0 ∧
      ∀ s ∈ Ioo A B, trajectory q v x s ∈ linePreimage q U F 0 v :=
  ⟨linePreimage_null q U hU F hF 0 v hv,
    backward_endpoint_tail_in_linePreimage q v x U hU F hF A B hAB hD hstay b₀ hb₀ hFb₀ hlim⟩

end MNEC.NativePrimitiveEndpoint

