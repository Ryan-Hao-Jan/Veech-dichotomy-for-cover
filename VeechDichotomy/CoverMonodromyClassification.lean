module

public import VeechDichotomy.CoverMonodromyStabilizer

/-! Equivariant fiber maps lift to actual maps of connected ordinary
covers. An equivariant fiber bijection gives an actual cover homeomorphism.
The proof uses the proved stabilizer criterion and native homotopy lifting;
an isomorphism or realization theorem is not supplied as a hypothesis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CoverMonodromyClassification

open Set Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} (cp : IsCoveringMap p) (cq : IsCoveringMap q)

def Equivariant {x : X} (h : (p ⁻¹' {x}) → (q ⁻¹' {x})) : Prop :=
  ∀ (γ : FundamentalGroup X x) (a : p ⁻¹' {x}),
    h (cp.monodromyPerm x γ a) = cq.monodromyPerm x γ (h a)

theorem exists_lift [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {x : X} (h : (p ⁻¹' {x}) → (q ⁻¹' {x})) (hh : Equivariant cp cq h)
    (a : p ⁻¹' {x}) :
    ∃ f : C(E, F), f a.val = (h a).val ∧ q ∘ f = p := by
  rcases a with ⟨a, ha⟩
  subst x
  have hr : (FundamentalGroup.map ⟨p, cp.continuous⟩ a).range ≤
      (FundamentalGroup.mapOfEq ⟨q, cq.continuous⟩ (h ⟨a, rfl⟩).property).range := by
    rintro γ ⟨η, rfl⟩
    apply (CoverMonodromyStabilizer.fixed_iff_range cq (h ⟨a, rfl⟩) _).mp
    rw [← hh _ ⟨a, rfl⟩]
    congr 1
    change cp.monodromy (η.asHom.map ⟨p, cp.continuous⟩) ⟨a, rfl⟩ = ⟨a, rfl⟩
    exact cp.monodromy_map η.asHom
  exact (cq.existsUnique_continuousMap_lifts_of_range_le
    (f := ⟨p, cp.continuous⟩) (h ⟨a, rfl⟩).property hr).exists

theorem symm_equivariant {x : X} (h : (p ⁻¹' {x}) ≃ (q ⁻¹' {x}))
    (hh : Equivariant cp cq h) : Equivariant cq cp h.symm := by
  intro γ b
  apply h.injective
  rw [Equiv.apply_symm_apply, hh, Equiv.apply_symm_apply]

theorem exists_homeomorph [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    {x : X} (h : (p ⁻¹' {x}) ≃ (q ⁻¹' {x})) (hh : Equivariant cp cq h)
    (a : p ⁻¹' {x}) :
    ∃ H : E ≃ₜ F, q ∘ H = p ∧ H a.val = (h a).val := by
  obtain ⟨f, hf, hpf⟩ := exists_lift cp cq h hh a
  obtain ⟨g, hg, hqg⟩ := exists_lift cq cp h.symm (symm_equivariant cp cq h hh) (h a)
  have hg' : g (h a).val = a.val := by
    simpa only [Equiv.symm_apply_apply] using hg
  have hgf : (g : F → E) ∘ f = id := by
    apply cp.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id _ a.val
    · change g (f a.val) = a.val
      rw [hf, hg']
    · funext z
      change p (g (f z)) = p z
      exact (congrFun hqg (f z)).trans (congrFun hpf z)
  have hfg : (f : E → F) ∘ g = id := by
    apply cq.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id _ (h a).val
    · change f (g (h a).val) = (h a).val
      rw [hg', hf]
    · funext z
      change q (f (g z)) = q z
      exact (congrFun hpf (g z)).trans (congrFun hqg z)
  let H : E ≃ₜ F :=
    { toFun := f
      invFun := g
      left_inv := congrFun hgf
      right_inv := congrFun hfg
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact ⟨H, hpf, hf⟩

end VeechDichotomy.CoverMonodromyClassification
