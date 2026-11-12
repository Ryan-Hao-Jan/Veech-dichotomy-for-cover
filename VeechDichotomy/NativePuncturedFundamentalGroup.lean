module

public import VeechDichotomy.NativeFundamentalGroup
public import VeechDichotomy.PuncturedCompactCore
public import Jacobians.MappingDegree.PathConnectedComplFinite

/-! Finite-punctured native compact connected complex curves have
finitely generated fundamental groups. The compact core and based loop
homotopies are constructed, and finite generators come from a finite net.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePuncturedFundamentalGroup

open Set Filter Topology FinitePunctureNeighborhoods
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem fundamentalGroup_fg {S : Set X} (hS : S.Finite) (o : outside S) :
    Group.FG (FundamentalGroup (outside S) o) := by
  let : SecondCountableTopology X := ChartedSpace.secondCountable_of_sigmaCompact ℂ X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : StronglyLocallyContractibleSpace X := ComplexContractibleNeighborhoods.stronglyLocallyContractible
  let : StronglyLocallyContractibleSpace (outside S) :=
    hS.isClosed.isOpen_compl.stronglyLocallyContractibleSpace
  let : LocallyPathConnectedSpace (outside S) := inferInstance
  let : PathConnectedSpace (outside S) := isPathConnected_iff_pathConnectedSpace.mp
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      hS ⟨o.val, o.property⟩)
  obtain ⟨K, hK, hoK, f, H, hfix, hRange⟩ := PuncturedCompactCore.exists_core hS o
  have hlocal (x : outside S) : ∃ U : Set (outside S), U ∈ 𝓝 x ∧ IsSimplyConnected U := by
    obtain ⟨U, ⟨hUx, hcon⟩, _⟩ := (contractible_basis x).mem_iff.mp (univ_mem : (univ : Set (outside S)) ∈ 𝓝 x)
    let : ContractibleSpace U := hcon
    exact ⟨U, hUx, by rw [IsSimplyConnected]; infer_instance⟩
  apply CompactFundamentalGroup.fg_of_compact_core hK hoK (fun x _ => hlocal x)
  intro γ
  obtain ⟨η, hη, hγη⟩ := BasedHomotopyLoops.exists_image_loop H o hfix γ
  exact ⟨η, hη.trans hRange, hγη⟩

end VeechDichotomy.NativePuncturedFundamentalGroup
