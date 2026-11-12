module

public import Jacobians.MappingDegree.IsPathConnectedBallMinusCountable
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.DenseEmbedding

/-! Complements of finite sets in actual complex curves have connected
neighborhoods at every added point. The neighborhoods are constructed from
punctured complex chart balls, with all finite obstructions removed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FinitePunctureNeighborhoods

open Set Filter Topology Metric

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

def outside (S : Set Y) : Set Y := Sᶜ

theorem connected_basis {S : Set Y} (hS : S.Finite) (a : Y)
    (s : Set (outside S)) (hs : s ∈ Filter.comap (Subtype.val : outside S → Y) (𝓝 a)) :
    ∃ t ∈ Filter.comap (Subtype.val : outside S → Y) (𝓝 a), t ⊆ s ∧ IsConnected t := by
  obtain ⟨U, hUa, hUsub⟩ := Filter.mem_comap.mp hs
  let c := chartAt ℂ a
  have ha : a ∈ c.source := mem_chart_source ℂ a
  have hinv : Tendsto c.symm (𝓝 (c a)) (𝓝 a) := by
    simpa only [c.left_inv ha] using (c.symm.continuousAt (c.map_source ha)).tendsto
  have hnear : c.target ∩ c.symm ⁻¹' U ∈ 𝓝 (c a) :=
    inter_mem (c.open_target.mem_nhds (c.map_source ha)) (hinv hUa)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let A : Set ℂ := c '' (c.source ∩ S)
  have hAfin : A.Finite := (hS.inter_of_right c.source).image c
  let K : Set ℂ := ball (c a) r \ A
  have hK : IsPathConnected K :=
    Jacobians.Discharge.Set.Countable.isPathConnected_ball_diff_complex hr hAfin.countable
  have hKtarget : K ⊆ c.target := fun _ hz => (hball hz.1).1
  have hKoutside : ∀ z ∈ K, c.symm z ∉ S := by
    intro z hz hzS
    apply hz.2
    exact ⟨c.symm z, ⟨c.map_target (hKtarget hz), hzS⟩, c.right_inv (hKtarget hz)⟩
  let g : K → outside S := fun z => ⟨c.symm z.val, hKoutside z.val z.property⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact c.symm.continuousOn.comp_continuous continuous_subtype_val fun z => hKtarget z.property
  have htconn : IsConnected (range g) := by
    let : PathConnectedSpace K := isPathConnected_iff_pathConnectedSpace.mp hK
    exact isConnected_range hg
  refine ⟨range g, ?_, ?_, htconn⟩
  · let W : Set Y := c.source ∩ c ⁻¹' ball (c a) r
    have hW : W ∈ 𝓝 a := inter_mem (c.open_source.mem_nhds ha)
      ((c.continuousAt ha) (ball_mem_nhds (c a) hr))
    apply Filter.mem_of_superset (Filter.preimage_mem_comap hW)
    intro y hy
    have hyA : c y.val ∉ A := by
      rintro ⟨z, ⟨hzc, hzS⟩, hzy⟩
      have heq : z = y.val := c.injOn hzc hy.1 hzy
      exact y.property (heq ▸ hzS)
    refine ⟨⟨c y.val, hy.2, hyA⟩, ?_⟩
    exact Subtype.ext (c.left_inv hy.1)
  · rintro _ ⟨z, rfl⟩
    exact hUsub ((hball z.property.1).2)

end VeechDichotomy.FinitePunctureNeighborhoods
