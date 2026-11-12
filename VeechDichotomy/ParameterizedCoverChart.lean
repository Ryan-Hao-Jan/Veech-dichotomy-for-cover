module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Actual open partial homeomorphisms for parameter-dependent pulled
charts. Both total chart domains are open in the product topologies and
both coordinate maps are jointly continuous, as consequences of the
constructed partial homeomorphism rather than pointwise continuity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ParameterizedCoverChart

variable {P X Y Z : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace Z]
variable (ψ : P → X ≃ₜ X)
  (hψ : Continuous (fun p : P × X => ψ p.1 p.2))
  (hInv : Continuous (fun p : P × X => (ψ p.1).symm p.2))

def homeomorph : P × X ≃ₜ P × X where
  toFun p := (p.1, ψ p.1 p.2)
  invFun p := (p.1, (ψ p.1).symm p.2)
  left_inv p := Prod.ext rfl ((ψ p.1).symm_apply_apply p.2)
  right_inv p := Prod.ext rfl ((ψ p.1).apply_symm_apply p.2)
  continuous_toFun := continuous_fst.prodMk hψ
  continuous_invFun := continuous_fst.prodMk hInv

def chart (e : OpenPartialHomeomorph Y X) (c : OpenPartialHomeomorph X Z) :
    OpenPartialHomeomorph (P × Y) (P × Z) :=
  (((OpenPartialHomeomorph.refl P).prod e).transHomeomorph (homeomorph ψ hψ hInv)).trans
    ((OpenPartialHomeomorph.refl P).prod c)

theorem chart_apply (e : OpenPartialHomeomorph Y X) (c : OpenPartialHomeomorph X Z) (p : P × Y) :
    chart ψ hψ hInv e c p = (p.1, c (ψ p.1 (e p.2))) := rfl

theorem chart_symm_apply (e : OpenPartialHomeomorph Y X) (c : OpenPartialHomeomorph X Z) (p : P × Z) :
    (chart ψ hψ hInv e c).symm p = (p.1, e.symm ((ψ p.1).symm (c.symm p.2))) := rfl

theorem mem_source_iff (e : OpenPartialHomeomorph Y X) (c : OpenPartialHomeomorph X Z) (p : P × Y) :
    p ∈ (chart ψ hψ hInv e c).source ↔ p.2 ∈ e.source ∧ ψ p.1 (e p.2) ∈ c.source := by
  change (p.1 ∈ Set.univ ∧ p.2 ∈ e.source) ∧
    (p.1 ∈ Set.univ ∧ ψ p.1 (e p.2) ∈ c.source) ↔ _
  simp only [Set.mem_univ, true_and]

theorem mem_target_iff (e : OpenPartialHomeomorph Y X) (c : OpenPartialHomeomorph X Z) (p : P × Z) :
    p ∈ (chart ψ hψ hInv e c).target ↔ p.2 ∈ c.target ∧ (ψ p.1).symm (c.symm p.2) ∈ e.target := by
  change (p.1 ∈ Set.univ ∧ p.2 ∈ c.target) ∧
    (p.1 ∈ Set.univ ∧ (ψ p.1).symm (c.symm p.2) ∈ e.target) ↔ _
  simp only [Set.mem_univ, true_and]

end VeechDichotomy.ParameterizedCoverChart
