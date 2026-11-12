module

public import VeechDichotomy.UniformSmallPaths
public import VeechDichotomy.SmallPathSubdivision
public import VeechDichotomy.LoopChainMembership
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.GroupTheory.Finiteness

/-! A compact subset of a locally path-connected metric space with small
simply connected neighborhoods has a finite set of based loops generating
all loop classes represented in that subset. The generators are constructed
from a finite metric net and chosen short edges. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CompactCoreLoopGenerators

open Set Metric Topology LoopChainMembership Path.Homotopic.Quotient

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [PseudoMetricSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]

theorem exists_generators {K : Set X} (hK : IsCompact K) {o : X} (ho : o ∈ K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, U ∈ 𝓝 x ∧ IsSimplyConnected U) :
    ∃ S : Set (FundamentalGroup X o), S.Finite ∧ ∀ γ : Path o o,
      range γ ⊆ K → FundamentalGroup.fromPath (mk γ) ∈ Subgroup.closure S := by
  classical
  obtain ⟨ε, hε, hhom⟩ := UniformSmallPaths.exists_uniform_homotopy_radius hK hlocal
  let r := ε / 8
  have hr : 0 < r := by dsimp [r]; linarith
  have hrε : r = ε / 8 := rfl
  obtain ⟨δ₀, hδ₀, hshort⟩ := UniformSmallPaths.exists_uniform_short_paths hK hr
  let δ := min δ₀ r
  have hδ : 0 < δ := lt_min hδ₀ hr
  have hδ₀bound : δ ≤ δ₀ := min_le_left _ _
  have hδr : δ ≤ r := min_le_right _ _
  have hδquarter : 0 < δ / 4 := by linarith
  obtain ⟨V, hVK, hVfin, hVcover⟩ := hK.finite_cover_balls hδquarter
  let : Finite V := hVfin.to_subtype
  have hex (x : K) : ∃ v : V, dist v.val x.val < δ / 4 := by
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hVcover x.property)
    obtain ⟨hvV, hxv⟩ := mem_iUnion.mp hv
    exact ⟨⟨v, hvV⟩, by simpa only [mem_ball, dist_comm] using hxv⟩
  choose nearest hnear using hex
  have hspoke (x : K) : ∃ p : Path x.val (nearest x).val, range p ⊆ ball x.val r :=
    hshort x.val x.property (nearest x).val (by
      have := hnear x
      linarith)
  choose nearPath hnearPath using hspoke
  let ref (v : V) : Path o v.val := PathConnectedSpace.somePath o v.val
  let edge (v w : V) : Path v.val w.val :=
    if h : dist w.val v.val < δ then
      Classical.choose (hshort v.val (hVK v.property) w.val (h.trans_le hδ₀bound))
    else PathConnectedSpace.somePath v.val w.val
  have hedge (v w : V) (h : dist w.val v.val < δ) : range (edge v w) ⊆ ball v.val r := by
    dsimp only [edge]
    rw [dite_eq_left h]
    exact Classical.choose_spec (hshort v.val (hVK v.property) w.val (h.trans_le hδ₀bound))
  let c (x : K) : Path o x.val := (ref (nearest x)).trans (nearPath x).symm
  let oK : K := ⟨o, ho⟩
  let gen : V × V → FundamentalGroup X o := fun vw => basedLoop (ref vw.1) (edge vw.1 vw.2) (ref vw.2)
  let S : Set (FundamentalGroup X o) := insert (FundamentalGroup.fromPath (mk (c oK))) (range gen)
  have hSfin : S.Finite := (finite_range gen).insert _
  let H := Subgroup.closure S
  have hbase : FundamentalGroup.fromPath (mk (c oK)) ∈ H :=
    Subgroup.subset_closure (Or.inl rfl)
  have hgen (v w : V) : basedLoop (ref v) (edge v w) (ref w) ∈ H :=
    Subgroup.subset_closure (Or.inr ⟨(v, w), rfl⟩)
  refine ⟨S, hSfin, ?_⟩
  intro γ hγ
  obtain ⟨n, t, ht0, ht1, hpiece⟩ := SmallPathSubdivision.exists_subdivision γ hδquarter
  let point (j : Fin (n + 1)) : K := ⟨γ (t j), hγ (mem_range_self _)⟩
  let s (j : Fin (n + 1)) : Path o (γ (t j)) := c (point j)
  apply loop_mem_of_subdivision H γ t ht0 ht1 s
  · intro k
    let x := point k.castSucc
    let y := point k.succ
    let v := nearest x
    let w := nearest y
    let p := γ.subpath (t k.castSucc) (t k.succ)
    have hyx : dist y.val x.val < δ / 4 := hpiece k p.target_mem_range
    have hvx : dist v.val x.val < δ / 4 := hnear x
    have hwy : dist w.val y.val < δ / 4 := hnear y
    have hwv : dist w.val v.val < δ := by
      have h₁ := dist_triangle w.val y.val v.val
      have h₂ := dist_triangle y.val x.val v.val
      rw [dist_comm x.val v.val] at h₂
      linarith
    let shortcut := (nearPath x).trans ((edge v w).trans (nearPath y).symm)
    have hpball : range p ⊆ ball x.val ε :=
      (hpiece k).trans (ball_subset_ball (by linarith))
    have hshortcut : range shortcut ⊆ ball x.val ε := by
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      refine union_subset ?_ (union_subset ?_ ?_)
      · intro z hz
        have hdz : dist z x.val < r := hnearPath x hz
        change dist z x.val < ε
        linarith
      · intro z hz
        have hdz : dist z v.val < r := hedge v w hwv hz
        change dist z x.val < ε
        have htri := dist_triangle z v.val x.val
        linarith
      · intro z hz
        have hdz : dist z y.val < r := hnearPath y hz
        change dist z x.val < ε
        have htri := dist_triangle z y.val x.val
        linarith
    have hpath : p.Homotopic shortcut := hhom x.val x.property p shortcut hpball hshortcut
    have heq := basedLoop_shortcut (ref v) (ref w) (nearPath x) (nearPath y) (edge v w) p hpath
    change basedLoop (c x) p (c y) ∈ H
    rw [heq]
    exact hgen v w
  · intro j hj
    have hjK : point j = oK := Subtype.ext hj
    have heq : (s j).cast rfl hj.symm = c oK := by
      ext u
      change c (point j) u = c oK u
      exact congrArg (fun x : K => c x u) hjK
    rw [heq]
    exact hbase

end VeechDichotomy.CompactCoreLoopGenerators
