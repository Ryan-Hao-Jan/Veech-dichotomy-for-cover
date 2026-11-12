module

public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! Subgroup membership for finite chains of based path loops. The
telescoping cancels the intermediate spokes and respects mathlib's
endomorphism multiplication convention. The proof generalizes the generic
telescoping argument in the supplied Jacobians SphereTopology/VanKampen
development from null loops to membership in any subgroup. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.LoopChainMembership

open Path.Homotopic.Quotient

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] {o a b c : X}

def basedLoop (s : Path o a) (p : Path a b) (t : Path o b) : FundamentalGroup X o :=
  FundamentalGroup.fromPath ((mk s).trans ((mk p).trans (mk t).symm))

theorem basedLoop_refl (s : Path o a) : basedLoop s (Path.refl a) s = 1 := by
  apply CategoryTheory.End.ext
  change (mk s).trans ((mk (Path.refl a)).trans (mk s).symm) = Path.Homotopic.Quotient.refl o
  rw [mk_refl, refl_trans, trans_symm]

theorem basedLoop_trans (s : Path o a) (p : Path a b) (t : Path o b)
    (q : Path b c) (u : Path o c) :
    basedLoop s (p.trans q) u = basedLoop t q u * basedLoop s p t := by
  apply CategoryTheory.End.ext
  change (mk s).trans ((mk (p.trans q)).trans (mk u).symm) =
    ((mk s).trans ((mk p).trans (mk t).symm)).trans ((mk t).trans ((mk q).trans (mk u).symm))
  rw [mk_trans]
  simp only [trans_assoc]
  rw [← trans_assoc (mk t).symm (mk t), symm_trans, refl_trans]

theorem basedLoop_eq_mul (s p t : Path o o) :
    basedLoop s p t = (FundamentalGroup.fromPath (mk t))⁻¹ *
      FundamentalGroup.fromPath (mk p) * FundamentalGroup.fromPath (mk s) := rfl

theorem path_mem_of_basedLoop_mem (H : Subgroup (FundamentalGroup X o))
    (s : Path o a) (p : Path a b) (t : Path o b) (ha : a = o) (hb : b = o)
    (hs : FundamentalGroup.fromPath (mk (s.cast rfl ha.symm)) ∈ H)
    (ht : FundamentalGroup.fromPath (mk (t.cast rfl hb.symm)) ∈ H)
    (hloop : basedLoop s p t ∈ H) :
    FundamentalGroup.fromPath (mk (p.cast ha.symm hb.symm)) ∈ H := by
  cases ha
  cases hb
  change FundamentalGroup.fromPath (mk s) ∈ H at hs
  change FundamentalGroup.fromPath (mk t) ∈ H at ht
  change FundamentalGroup.fromPath (mk p) ∈ H
  simpa only [basedLoop_eq_mul, mul_assoc, mul_inv_cancel, one_mul, mul_one, mul_inv_cancel_left] using
    H.mul_mem (H.mul_mem ht hloop) (H.inv_mem hs)

theorem basedLoop_congr (s : Path o a) (t : Path o b) {p q : Path a b} (hp : p.Homotopic q) :
    basedLoop s p t = basedLoop s q t := by
  apply CategoryTheory.End.ext
  change (mk s).trans ((mk p).trans (mk t).symm) = (mk s).trans ((mk q).trans (mk t).symm)
  rw [Path.Homotopic.Quotient.eq.mpr hp]

theorem basedLoop_shortcut {v w : X} (s : Path o v) (t : Path o w)
    (u : Path a v) (z : Path b w) (e : Path v w) (p : Path a b)
    (hp : p.Homotopic (u.trans (e.trans z.symm))) :
    basedLoop (s.trans u.symm) p (t.trans z.symm) = basedLoop s e t := by
  rw [basedLoop_congr _ _ hp]
  apply CategoryTheory.End.ext
  change (mk (s.trans u.symm)).trans
      ((mk (u.trans (e.trans z.symm))).trans (mk (t.trans z.symm)).symm) =
    (mk s).trans ((mk e).trans (mk t).symm)
  rw [← mk_symm, Path.trans_symm, Path.symm_symm]
  simp only [mk_trans, mk_symm, trans_assoc]
  rw [← trans_assoc (mk u).symm (mk u), symm_trans, refl_trans,
    ← trans_assoc (mk z).symm (mk z), symm_trans, refl_trans]

theorem concat_mem (H : Subgroup (FundamentalGroup X o)) :
    ∀ {n : ℕ} (q : Fin (n + 1) → X) (s : ∀ j, Path o (q j))
      (F : ∀ k : Fin n, Path (q k.castSucc) (q k.succ)),
      (∀ k, basedLoop (s k.castSucc) (F k) (s k.succ) ∈ H) →
      basedLoop (s 0) (Path.concat q F) (s (Fin.last n)) ∈ H := by
  intro n
  induction n with
  | zero =>
    intro q s F _
    rw [Path.concat_zero]
    change basedLoop (s 0) (Path.refl (q 0)) (s 0) ∈ H
    rw [basedLoop_refl]
    exact H.one_mem
  | succ n ih =>
    intro q s F hmem
    rw [Path.concat_succ, basedLoop_trans (t := s (Fin.last n).castSucc)]
    exact H.mul_mem (hmem (Fin.last n))
      (ih (q ∘ Fin.castSucc) (fun j => s j.castSucc) (fun k => F k.castSucc)
        (fun k => hmem k.castSucc))

theorem loop_mem_of_subdivision (H : Subgroup (FundamentalGroup X o)) (γ : Path o o)
    {n : ℕ} (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (s : ∀ j, Path o (γ (t j)))
    (hedge : ∀ k : Fin n, basedLoop (s k.castSucc)
      (γ.subpath (t k.castSucc) (t k.succ)) (s k.succ) ∈ H)
    (hends : ∀ j (hj : γ (t j) = o),
      FundamentalGroup.fromPath (mk ((s j).cast rfl hj.symm)) ∈ H) :
    FundamentalGroup.fromPath (mk γ) ∈ H := by
  have h0 : γ (t 0) = o := by rw [ht0]; exact γ.source
  have h1 : γ (t (Fin.last n)) = o := by rw [ht1]; exact γ.target
  let F := fun k : Fin n => γ.subpath (t k.castSucc) (t k.succ)
  have hconcat := path_mem_of_basedLoop_mem H (s 0) (Path.concat (γ ∘ t) F)
    (s (Fin.last n)) h0 h1 (hends 0 h0) (hends (Fin.last n) h1)
    (concat_mem H (γ ∘ t) s F hedge)
  have hhom := (Path.Homotopic.concat_subpath γ t).pathCast h0.symm h1.symm
  have hsub : (γ.subpath (t 0) (t (Fin.last n))).cast h0.symm h1.symm = γ := by
    ext u
    change γ (Set.Icc.convexComb (t 0) (t (Fin.last n)) u) = γ u
    rw [ht0, ht1, Set.Icc.convexComb_zero_one]
  rw [hsub] at hhom
  have heq : FundamentalGroup.fromPath (mk ((Path.concat (γ ∘ t) F).cast h0.symm h1.symm)) =
      FundamentalGroup.fromPath (mk γ) :=
    congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr hhom)
  rwa [heq] at hconcat

end VeechDichotomy.LoopChainMembership
