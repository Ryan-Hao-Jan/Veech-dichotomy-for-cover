module

public import VeechDichotomy.DisjointPointTransport
public import Mathlib.Topology.UnitInterval

/-! Scaling the small displacement coordinates gives an explicit isotopy
through actual whole-surface homeomorphisms, with jointly continuous inverse.
This keeps local branch transport in the identity isotopy class.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PointTransportIsotopy

open Set Topology unitInterval LocalTranslationPlane DisjointPointTransport

set_option backward.isDefEq.respectTransparency false

def scaleParameter (t : I) (δ : Parameter) : Parameter :=
  ⟨(t : ℝ) • δ.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    have hle : (t : ℝ) * ‖δ.val‖ ≤ ‖δ.val‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg δ.val)
    exact hle.trans_lt δ.property⟩

theorem scaleParameter_zero (δ : Parameter) : scaleParameter 0 δ = zeroParameter := by
  apply Subtype.ext
  exact zero_smul ℝ δ.val

theorem scaleParameter_one (δ : Parameter) : scaleParameter 1 δ = δ := by
  apply Subtype.ext
  exact one_smul ℝ δ.val

def scaleTuple {ι : Type*} (δ : ι → Parameter) (t : I) : ι → Parameter := fun i => scaleParameter t (δ i)

theorem continuous_scaleTuple {ι : Type*} (δ : ι → Parameter) : Continuous (scaleTuple δ) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact continuous_subtype_val.smul continuous_const

theorem exists_isotopy {X ι : Type*} [TopologicalSpace X]
    (F : (ι → Parameter) → X ≃ₜ X)
    (hF : Continuous (fun p : (ι → Parameter) × X => F p.1 p.2))
    (hInv : Continuous (fun p : (ι → Parameter) × X => (F p.1).symm p.2))
    (hzero : F (fun _ => zeroParameter) = Homeomorph.refl X) (δ : ι → Parameter) :
    ∃ J : I → X ≃ₜ X, J 0 = Homeomorph.refl X ∧ J 1 = F δ ∧
      Continuous (fun p : I × X => J p.1 p.2) ∧
      Continuous (fun p : I × X => (J p.1).symm p.2) := by
  let J : I → X ≃ₜ X := fun t => F (scaleTuple δ t)
  have h0 : scaleTuple δ 0 = fun _ => zeroParameter := funext fun i => scaleParameter_zero (δ i)
  have h1 : scaleTuple δ 1 = δ := funext fun i => scaleParameter_one (δ i)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · change F (scaleTuple δ 0) = _
    rw [h0, hzero]
  · change F (scaleTuple δ 1) = _
    rw [h1]
  · exact hF.comp (((continuous_scaleTuple δ).comp continuous_fst).prodMk continuous_snd)
  · exact hInv.comp (((continuous_scaleTuple δ).comp continuous_fst).prodMk continuous_snd)

end VeechDichotomy.PointTransportIsotopy
