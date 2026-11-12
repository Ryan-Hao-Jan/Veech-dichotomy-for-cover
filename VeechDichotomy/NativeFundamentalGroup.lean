module

public import VeechDichotomy.ComplexContractibleNeighborhoods
public import VeechDichotomy.CompactFundamentalGroup
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Metrizable.Uniformity

/-! Actual compact connected complex curves have finitely generated
fundamental groups. A compatible metric is constructed from their native
topology; local contractibility comes from their actual complex charts.
Finite-punctured curves require the separate compact-core construction.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFundamentalGroup

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]

theorem fundamentalGroup_fg (o : X) : Group.FG (FundamentalGroup X o) := by
  let : SecondCountableTopology X := ChartedSpace.secondCountable_of_sigmaCompact ℂ X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : StronglyLocallyContractibleSpace X := ComplexContractibleNeighborhoods.stronglyLocallyContractible
  let : LocallyPathConnectedSpace X := inferInstance
  let : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  exact CompactFundamentalGroup.fg_of_compact o ComplexContractibleNeighborhoods.exists_simplyConnected_neighborhood

end VeechDichotomy.NativeFundamentalGroup
