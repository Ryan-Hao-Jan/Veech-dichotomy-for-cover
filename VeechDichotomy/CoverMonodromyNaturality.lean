module

public import VeechDichotomy.CoverMonodromyClassification

/-! Actual maps commuting with covering projections intertwine monodromy.
Together with the construction in CoverMonodromyClassification, this gives
both directions of ordinary-cover classification by equivariant fibers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CoverMonodromyNaturality

open Set Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} (cp : IsCoveringMap p) (cq : IsCoveringMap q)

def fiberMap (f : C(E, F)) (hsquare : q ∘ f = p) {x : X} : (p ⁻¹' {x}) → (q ⁻¹' {x}) :=
  fun a => ⟨f a.val, (congrFun hsquare a.val).trans a.property⟩

theorem monodromy_commutes (f : C(E, F)) (hsquare : q ∘ f = p)
    {x y : X} (γ : Path.Homotopic.Quotient x y) (a : p ⁻¹' {x}) :
    fiberMap f hsquare (cp.monodromy γ a) = cq.monodromy γ (fiberMap f hsquare a) := by
  obtain ⟨γ⟩ := γ
  let Γ := cp.liftPath γ a.val (γ.source.trans a.property.symm)
  have hΓ0 : Γ 0 = a.val := cp.liftPath_zero _ _ _
  have hlift : q ∘ (f.comp Γ) = γ := by
    funext t
    exact (congrFun hsquare (Γ t)).trans
      (congrFun (cp.liftPath_lifts γ a.val (γ.source.trans a.property.symm)) t)
  have hstart : (f.comp Γ) 0 = (fiberMap f hsquare a).val := by
    change f (Γ 0) = f a.val
    rw [hΓ0]
  have hend := cq.monodromy_eq_apply_one hlift hstart
  apply Subtype.ext
  exact hend.symm

theorem equivariant (f : C(E, F)) (hsquare : q ∘ f = p) {x : X} :
    CoverMonodromyClassification.Equivariant cp cq (fiberMap f hsquare (x := x)) :=
  fun γ a => monodromy_commutes cp cq f hsquare γ.asHom a

def fiberEquiv (H : E ≃ₜ F) (hsquare : q ∘ H = p) {x : X} : (p ⁻¹' {x}) ≃ (q ⁻¹' {x}) where
  toFun := fiberMap ⟨H, H.continuous⟩ hsquare
  invFun b := ⟨H.symm b.val, by
    have h := congrFun hsquare (H.symm b.val)
    change q (H (H.symm b.val)) = p (H.symm b.val) at h
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm.trans b.property⟩
  left_inv a := Subtype.ext (H.symm_apply_apply a.val)
  right_inv b := Subtype.ext (H.apply_symm_apply b.val)

theorem exists_homeomorph_iff [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F] {x : X} (a : p ⁻¹' {x}) :
    (∃ H : E ≃ₜ F, q ∘ H = p) ↔
      ∃ h : (p ⁻¹' {x}) ≃ (q ⁻¹' {x}), CoverMonodromyClassification.Equivariant cp cq h := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨fiberEquiv H hH, equivariant cp cq ⟨H, H.continuous⟩ hH⟩
  · rintro ⟨h, hh⟩
    obtain ⟨H, hH, _⟩ := CoverMonodromyClassification.exists_homeomorph cp cq h hh a
    exact ⟨H, hH⟩

end VeechDichotomy.CoverMonodromyNaturality
