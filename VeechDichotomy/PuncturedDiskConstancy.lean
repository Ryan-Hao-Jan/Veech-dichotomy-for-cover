module

public import Jacobians.MappingDegree.IsPathConnectedBallMinusCountable
public import Mathlib.Topology.LocallyConstant.Basic

/-! A function continuous at a complex disk center and locally constant
off that center is constant on the whole disk. Connectedness of the
actual punctured complex disk removes the missing center. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PuncturedDiskConstancy

open Set Filter Topology

theorem eq_center {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (g : ℂ → Y) {r : ℝ} (hr : 0 < r) (hzero : ContinuousAt g 0)
    (hlocal : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → ∀ᶠ w in 𝓝 z, g w = g z) :
    ∀ z ∈ Metric.ball (0 : ℂ) r, g z = g 0 := by
  let B := Metric.ball (0 : ℂ) r \ {0}
  have hpath : IsPathConnected B :=
    Jacobians.Discharge.Set.Countable.isPathConnected_ball_diff_complex hr (finite_singleton (0 : ℂ)).countable
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hpath.isConnected.isPreconnected
  have hconst : IsLocallyConstant (fun z : B => g z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.tendsto (hlocal z.val z.property.1 z.property.2)
  obtain ⟨u, hu, _⟩ := hpath
  have hvalues : ∀ z ∈ B, g z = g u := fun z hz =>
    hconst.apply_eq_of_preconnectedSpace (⟨z, hz⟩ : B) (⟨u, hu⟩ : B)
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = g u := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hr), self_mem_nhdsWithin] with z hzB hzN
    exact hvalues z ⟨hzB, hzN⟩
  have heq : g =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => g u) := hev
  have hlim : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g u)) := Tendsto.congr' heq.symm tendsto_const_nhds
  have hcenter : g 0 = g u := tendsto_nhds_unique hzero.continuousWithinAt.tendsto hlim
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    rfl
  · exact (hvalues z ⟨hz, hz0⟩).trans hcenter.symm

end VeechDichotomy.PuncturedDiskConstancy
