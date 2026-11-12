module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith

/-! Every actual path admits a finite subdivision whose pieces lie in
arbitrarily small metric balls about their initial points. This uses the
proved subdivision theorem for an open cover of the compact unit interval.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SmallPathSubdivision

open Set Metric Topology unitInterval

variable {X : Type*} [PseudoMetricSpace X] {a b : X}

theorem exists_subdivision (γ : Path a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ ball (γ (t k.castSucc)) ε := by
  obtain ⟨u, hu0, humono, ⟨N, hN⟩, hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun x : X => γ ⁻¹' ball x (ε / 2))
      (fun x : X => isOpen_ball.preimage γ.continuous)
      (fun s _ => mem_iUnion.mpr ⟨γ s, mem_ball_self (half_pos hε)⟩)
  refine ⟨N, fun j => u j.val, hu0, hN N le_rfl, ?_⟩
  intro k
  obtain ⟨x, hx⟩ := hpieces k.val
  have hu : u k.val ≤ u (k.val + 1) := humono (Nat.le_succ k.val)
  have hstart : dist (γ (u k.val)) x < ε / 2 := hx ⟨le_rfl, hu⟩
  intro z hz
  rw [Path.range_subpath] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hs' : s ∈ Icc (u k.val) (u (k.val + 1)) := by
    simpa only [uIcc_of_le hu, Fin.val_castSucc, Fin.val_succ] using hs
  have hpoint : dist (γ s) x < ε / 2 := hx hs'
  change dist (γ s) (γ (u k.val)) < ε
  have htriangle := dist_triangle (γ s) x (γ (u k.val))
  rw [dist_comm x (γ (u k.val))] at htriangle
  linarith

end VeechDichotomy.SmallPathSubdivision
