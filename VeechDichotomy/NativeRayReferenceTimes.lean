module

public import VeechDichotomy.NativeRayRectangleComparison

/-! The actual inverse contraction is a positive divergent reference
time. Source times lifted from bounded ray times have EXACTLY those ray
times as their ratios to the reference, including negative time shifts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayReferenceTimes

open MNEC.LatticeTorus Set Filter Topology

def reference (v : Plane) (t : ℝ) : ℝ := (NativeTeichmullerRay.contraction v t)⁻¹

theorem reference_pos (v : Plane) (hv : v ≠ 0) (t : ℝ) : 0 < reference v t :=
  inv_pos.mpr (NativeTeichmullerRay.contraction_pos v hv t)

theorem reference_tendsto {I : Type*} {l : Filter I} (v : Plane) (hv : v ≠ 0)
    {t : I → ℝ} (ht : Tendsto t l atTop) : Tendsto (fun i => reference v (t i)) l atTop := by
  simpa only [reference, one_div] using NativeRayRectangleComparison.lifted_time_tendsto v hv ht
    (tendsto_const_nhds : Tendsto (fun _ : I => (1 : ℝ)) l (𝓝 1)) zero_lt_one

theorem lifted_ratio (v : Plane) (hv : v ≠ 0) (t L : ℝ) :
    (L / NativeTeichmullerRay.contraction v t) / reference v t = L := by
  rw [reference, ← one_div (NativeTeichmullerRay.contraction v t),
    div_div_div_cancel_right₀ (NativeTeichmullerRay.contraction_pos v hv t).ne', div_one]

theorem lifted_ratio_tendsto {I : Type*} {l : Filter I} (v : Plane) (hv : v ≠ 0) (t L : I → ℝ)
    {a : ℝ} (hL : Tendsto L l (𝓝 a)) :
    Tendsto (fun i => (L i / NativeTeichmullerRay.contraction v (t i)) / reference v (t i)) l (𝓝 a) := by
  exact Tendsto.congr (fun i => (lifted_ratio v hv (t i) (L i)).symm) hL

end VeechDichotomy.NativeRayReferenceTimes
