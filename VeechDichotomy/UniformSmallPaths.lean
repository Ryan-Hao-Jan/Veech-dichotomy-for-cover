module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith

/-! Uniform short-path and local homotopy bounds above a compact subset.
These are the analytic-topological estimates used to replace loops by
paths on a finite graph. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformSmallPaths

open Set Filter Topology Metric

variable {X : Type*} [PseudoMetricSpace X]

theorem homotopic_of_ranges {U : Set X} (hU : IsSimplyConnected U)
    {a b : X} (p q : Path a b) (hp : range p ⊆ U) (hq : range q ⊆ U) : p.Homotopic q := by
  have : SimplyConnectedSpace U := hU.simplyConnectedSpace
  let a' : U := ⟨a, hp p.source_mem_range⟩
  let b' : U := ⟨b, hp p.target_mem_range⟩
  let p' : Path a' b' :=
    { toFun := fun t => ⟨p t, hp (mem_range_self t)⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path a' b' :=
    { toFun := fun t => ⟨q t, hq (mem_range_self t)⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic p' q').map ⟨Subtype.val, continuous_subtype_val⟩

theorem exists_uniform_short_paths [LocallyPathConnectedSpace X] {K : Set X}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y : X, dist y x < δ →
      ∃ p : Path x y, range p ⊆ ball x ε := by
  classical
  have hlocal (a : K) : ∃ U : Set X, IsOpen U ∧ a.val ∈ U ∧ IsPathConnected U ∧
      U ⊆ ball a.val (ε / 2) := by
    obtain ⟨U, hU, hsub⟩ := (isOpen_isPathConnected_basis a.val).mem_iff.mp
      (ball_mem_nhds a.val (half_pos hε))
    exact ⟨U, hU.1, hU.2.1, hU.2.2, hsub⟩
  choose U hUopen hUmem hUpc hUsub using hlocal
  have hcover : K ⊆ ⋃ a : K, U a := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hUmem _⟩
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric hK hUopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hxy
  obtain ⟨a, ha⟩ := hLeb x hx
  have hxU : x ∈ U a := ha (mem_ball_self hδ)
  have hyU : y ∈ U a := ha hxy
  obtain ⟨p, hp⟩ := (hUpc a).joinedIn x hxU y hyU
  refine ⟨p, ?_⟩
  rintro _ ⟨t, rfl⟩
  have ht : dist (p t) a.val < ε / 2 := hUsub a (hp t)
  have hx' : dist x a.val < ε / 2 := hUsub a hxU
  change dist (p t) x < ε
  have htriangle := dist_triangle (p t) a.val x
  rw [dist_comm a.val x] at htriangle
  linarith

theorem exists_uniform_homotopy_radius {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, U ∈ 𝓝 x ∧ IsSimplyConnected U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ {a b : X} (p q : Path a b),
      range p ⊆ ball x ε → range q ⊆ ball x ε → p.Homotopic q := by
  classical
  choose U hUnhds hUsc using (fun a : K => hlocal a.val a.property)
  have hcover : K ⊆ ⋃ a : K, interior (U a) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hUnhds ⟨x, hx⟩)⟩
  obtain ⟨ε, hε, hLeb⟩ := lebesgue_number_lemma_of_metric hK (fun _ => isOpen_interior) hcover
  refine ⟨ε, hε, ?_⟩
  intro x hx a b p q hp hq
  obtain ⟨i, hi⟩ := hLeb x hx
  exact homotopic_of_ranges (hUsc i) p q (hp.trans (hi.trans interior_subset))
    (hq.trans (hi.trans interior_subset))

end VeechDichotomy.UniformSmallPaths
