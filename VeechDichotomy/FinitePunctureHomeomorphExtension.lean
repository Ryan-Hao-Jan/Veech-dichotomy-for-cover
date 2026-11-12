module

public import VeechDichotomy.FinitePunctureExtension

/-! An isomorphism of finite-punctured compact complex curves commuting
with continuous finite-fiber projections extends to an actual whole-curve
homeomorphism. The extensions and both inverse identities are derived. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FinitePunctureHomeomorphExtension

open Set Topology FinitePunctureNeighborhoods FinitePunctureExtension

variable {Y Z X : Type*}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ChartedSpace ℂ Z]
  [TopologicalSpace X] [T2Space X]

theorem exists_extension {S : Set Y} {T : Set Z} (hS : S.Finite) (hT : T.Finite)
    (p : Y → X) (hp : Continuous p) (hpf : ∀ x, (p ⁻¹' {x}).Finite)
    (q : Z → X) (hq : Continuous q) (hqf : ∀ x, (q ⁻¹' {x}).Finite)
    (h : outside S ≃ₜ outside T) (hsquare : ∀ y, q (h y).val = p y.val) :
    ∃ H : Y ≃ₜ Z, (∀ y : outside S, H y.val = (h y).val) ∧ q ∘ H = p := by
  have hsqInv : ∀ z : outside T, p (h.symm z).val = q z.val := by
    intro z
    simpa only [Homeomorph.apply_symm_apply] using (hsquare (h.symm z)).symm
  obtain ⟨f, hf, hqf'⟩ := FinitePunctureExtension.exists_extension hS
    (fun y => (h y).val) (continuous_subtype_val.comp h.continuous) q hq hqf p hp hsquare
  obtain ⟨g, hg, hpg'⟩ := FinitePunctureExtension.exists_extension hT
    (fun z => (h.symm z).val) (continuous_subtype_val.comp h.symm.continuous) p hp hpf q hq hsqInv
  have hgf : (g : Z → Y) ∘ f = id := by
    apply Continuous.ext_on (outside_dense hS) (g.continuous.comp f.continuous) continuous_id
    intro y hy
    change g (f y) = y
    calc
      g (f y) = g (h ⟨y, hy⟩).val := congrArg g (hf ⟨y, hy⟩)
      _ = (h.symm (h ⟨y, hy⟩)).val := hg _
      _ = y := congrArg Subtype.val (h.symm_apply_apply ⟨y, hy⟩)
  have hfg : (f : Y → Z) ∘ g = id := by
    apply Continuous.ext_on (outside_dense hT) (f.continuous.comp g.continuous) continuous_id
    intro z hz
    change f (g z) = z
    calc
      f (g z) = f (h.symm ⟨z, hz⟩).val := congrArg f (hg ⟨z, hz⟩)
      _ = (h (h.symm ⟨z, hz⟩)).val := hf _
      _ = z := congrArg Subtype.val (h.apply_symm_apply ⟨z, hz⟩)
  let H : Y ≃ₜ Z :=
    { toFun := f
      invFun := g
      left_inv := congrFun hgf
      right_inv := congrFun hfg
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact ⟨H, hf, hqf'⟩

end VeechDichotomy.FinitePunctureHomeomorphExtension
