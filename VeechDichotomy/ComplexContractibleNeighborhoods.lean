module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Actual complex chart balls give contractible open neighborhoods,
including arbitrarily small ones. No local contractibility certificate
is required of a native complex curve. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexContractibleNeighborhoods

open Set Filter Topology Metric

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem exists_contractible_open_subset (x : X) (V : Set X) (hV : V ∈ 𝓝 x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ ContractibleSpace U := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hi : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv hx] using (c.symm.continuousAt (c.map_source hx)).tendsto
  have hnear : c.target ∩ c.symm ⁻¹' V ∈ 𝓝 (c x) :=
    inter_mem (c.open_target.mem_nhds (c.map_source hx)) (hi hV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let D := ball (c x) r
  let U := c.symm '' D
  have hD : D ⊆ c.target := fun _ hz => (hball hz).1
  have hU : IsOpen U := c.symm.isOpen_image_of_subset_source isOpen_ball hD
  have hxU : x ∈ U := ⟨c x, mem_ball_self hr, c.left_inv hx⟩
  have hUV : U ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hhomeo : D ≃ₜ U := c.symm.homeomorphOfImageSubsetSource hD rfl
  have : ContractibleSpace D := contractibleSpace_ball hr
  exact ⟨U, hU, hxU, hUV, hhomeo.symm.contractibleSpace⟩

theorem stronglyLocallyContractible : StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    rw [Filter.hasBasis_self]
    intro V hV
    obtain ⟨U, hU, hxU, hUV, hcon⟩ := exists_contractible_open_subset x V hV
    exact ⟨U, hU.mem_nhds hxU, hcon, hUV⟩

theorem exists_simplyConnected_neighborhood (x : X) :
    ∃ U : Set X, U ∈ 𝓝 x ∧ IsSimplyConnected U := by
  obtain ⟨U, hU, hxU, _, hcon⟩ := exists_contractible_open_subset x univ univ_mem
  have : ContractibleSpace U := hcon
  exact ⟨U, hU.mem_nhds hxU, by
    rw [IsSimplyConnected]
    infer_instance⟩

end VeechDichotomy.ComplexContractibleNeighborhoods
