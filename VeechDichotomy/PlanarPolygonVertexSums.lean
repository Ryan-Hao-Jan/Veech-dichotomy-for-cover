module

public import VeechDichotomy.OrderedPolygonNormalCones

/-! Literal finite vertex sums for actual strictly ray-ordered complex
polygons. The root is absent from the chain and the chain is injective,
so every actual vertex is counted once in the corner-angle bookkeeping. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PlanarPolygonVertexSums

open Set ComplexOrientedTriangles OrderedPlanarFans

local instance : DecidableEq ℂ := Classical.decEq _

noncomputable def vertexFinset (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Finset ℂ := by
  classical
  exact insert a ((Finset.range (n + 1)).image v)

theorem coe_vertexFinset (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : (vertexFinset a v n : Set ℂ) = vertices a v n := by
  classical
  ext z
  simp [vertexFinset, vertices]

theorem root_ne_chain {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (hn : 0 < n) (h : OrderedRays a v n)
    (i : ℕ) (hi : i ≤ n) : a ≠ v i := by
  by_cases hz : i = 0
  · subst i
    exact (PlanarFanIntersections.positive_distinct (h 0 n hn le_rfl)).1
  · exact (PlanarFanIntersections.positive_distinct (h 0 i (Nat.pos_of_ne_zero hz) hi)).2.1

theorem chain_injective {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : OrderedRays a v n) : InjOn v (Iic n) := by
  intro i hi j hj he
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (PlanarFanIntersections.positive_distinct (h i j hlt hj)).2.2 he
  · exact (PlanarFanIntersections.positive_distinct (h j i hgt hi)).2.2 he.symm

theorem root_not_mem_image {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (hn : 0 < n) (h : OrderedRays a v n) :
    a ∉ (Finset.range (n + 1)).image v := by
  classical
  rintro hm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  exact root_ne_chain hn h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) he.symm

theorem sum_vertices (f : ℂ → ℝ) (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : OrderedRays a v n) :
    (∑ z ∈ vertexFinset a v n, f z) = f a + f (v 0) +
      (∑ i ∈ Finset.range (n - 1), f (v (i + 1))) + f (v n) := by
  classical
  have himage : (∑ z ∈ (Finset.range (n + 1)).image v, f z) = ∑ i ∈ Finset.range (n + 1), f (v i) :=
    Finset.sum_image (fun i hi j hj he => chain_injective h
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) he)
  have hfirst : (∑ i ∈ Finset.range n, f (v i)) =
      (∑ i ∈ Finset.range (n - 1), f (v (i + 1))) + f (v 0) := by
    simpa only [Nat.sub_add_cancel hn] using Finset.sum_range_succ' (fun i => f (v i)) (n - 1)
  rw [vertexFinset, Finset.sum_insert (root_not_mem_image hn h), himage, Finset.sum_range_succ, hfirst]
  ring

theorem vertexFinset_eq {a : ℂ} {v : ℕ → ℂ} {n : ℕ} {S : Finset ℂ}
    (h : vertices a v n = (S : Set ℂ)) : vertexFinset a v n = S := by
  apply Finset.coe_injective
  rw [coe_vertexFinset, h]

end VeechDichotomy.PlanarPolygonVertexSums
