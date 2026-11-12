module

public import VeechDichotomy.NativeAffineNormalization
public import VeechDichotomy.NativeDifferentialEquivalenceLaws
public import VeechDichotomy.ConfigurationSpace
public import MNEC.NativeDifferentialEquivFlatness

/-! On the constructed deformations of one fixed native differential,
the affine marked relation is exactly existence of a genuine differential
equivalence carrying the specified marks. This is an identification of
objects and equivalences; no ambient moduli topology is asserted here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeMarkedOrbitEquivalence

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech LinearGroup LinearEquivalences WholeDeformedAtlas NativeDeformationRegular
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)

def conjugateSurface {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) : X ≃ₜ X :=
  (((toOriginal q B).symm).trans e.homeomorph).trans (toOriginal q A)

def conjugateRegular {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) : Regular q ≃ₜ Regular q :=
  ((regularHomeomorph q B).trans (MNEC.NativeDifferentialEquiv.regularHomeomorph e)).trans
    (regularHomeomorph q A).symm

theorem conjugateRegular_value {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) (x : Regular q) :
    (conjugateRegular q e x).val = conjugateSurface q e x.val := rfl

theorem conjugateRegular_derivative {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) (x : Regular q) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (conjugateRegular q e) x (linear (A⁻¹ * B)) := by
  have hB := hasMFDerivAt_regularHomeomorph q B x
  have he := MNEC.NativeDifferentialEquivFlatness.hasMFDerivAt_regularHomeomorph e
    (regularHomeomorph q B x)
  have hA := hasMFDerivAt_regularHomeomorph_symm q A
    (MNEC.NativeDifferentialEquiv.regularHomeomorph e (regularHomeomorph q B x))
  have hcomp := hA.comp x (he.comp x hB)
  have hlin : (planeEquiv A).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ Plane).comp (planeEquiv B).toContinuousLinearMap) = linear (A⁻¹ * B) := by
    rw [ContinuousLinearMap.id_comp]
    exact (linear_mul A⁻¹ B).symm
  rw [hlin] at hcomp
  exact hcomp

theorem conjugateRegular_inverse_derivative {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) (x : Regular q) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (conjugateRegular q e).symm x (linear (A⁻¹ * B)⁻¹) := by
  have hA := hasMFDerivAt_regularHomeomorph q A x
  have he := MNEC.NativeDifferentialEquivFlatness.hasMFDerivAt_regularHomeomorph_symm e
    (regularHomeomorph q A x)
  have hB := hasMFDerivAt_regularHomeomorph_symm q B
    ((MNEC.NativeDifferentialEquiv.regularHomeomorph e).symm (regularHomeomorph q A x))
  have hcomp := hB.comp x (he.comp x hA)
  have hlin : (planeEquiv B).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ Plane).comp (planeEquiv A).toContinuousLinearMap) = linear (A⁻¹ * B)⁻¹ := by
    rw [ContinuousLinearMap.id_comp, mul_inv_rev, inv_inv]
    exact (linear_mul B⁻¹ A).symm
  rw [hlin] at hcomp
  exact hcomp

def conjugateAffine {A B : SL2}
    (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q B) (transformed q A)) :
    AffineAutomorphism q (A⁻¹ * B) where
  surface := conjugateSurface q e
  regular := conjugateRegular q e
  value := conjugateRegular_value q e
  derivative := conjugateRegular_derivative q e
  inverse_derivative := conjugateRegular_inverse_derivative q e

def NativeRelation {m : ℕ} (u v : SL2 × (Fin m → X)) : Prop :=
  ∃ e : MNEC.NativeDifferentialEquiv.Equiv (transformed q v.1) (transformed q u.1),
    ∀ i, e.homeomorph ((toOriginal q v.1).symm (v.2 i)) = (toOriginal q u.1).symm (u.2 i)

theorem nativeRelation_of_markedRelation {m : ℕ} (u v : SL2 × (Fin m → X))
    (h : (markedRelation (Z := Fin m → X) (NativeAffineGroup.derivative q)).r u v) :
    NativeRelation q u v := by
  rcases u with ⟨A, b⟩
  rcases v with ⟨B, c⟩
  obtain ⟨a, hA, hb⟩ := h
  change B = A * NativeAffineGroup.derivative q a at hA
  change c = a⁻¹ • b at hb
  subst B
  subst c
  obtain ⟨γ, φ, hφ⟩ := a.property
  have hγ : γ = NativeAffineGroup.derivative q a := congrArg (fun w : NativeAffineGroup.Raw q => w.2.2) hφ
  have haRaw : a.val = NativeAffineGroup.asRaw φ := hφ.symm
  subst γ
  refine ⟨NativeAffineNormalization.equivalence q φ A, ?_⟩
  intro i
  have hmark : (a⁻¹ • b) i = φ.surface.symm (b i) := by
    change (a.val⁻¹).1 (b i) = _
    rw [haRaw]
    rfl
  change (NativeAffineNormalization.equivalence q φ A).homeomorph
    ((toOriginal q (A * NativeAffineGroup.derivative q a)).symm ((a⁻¹ • b) i)) = _
  rw [hmark]
  exact NativeAffineNormalization.equivalence_normalized_mark q φ A (b i)

theorem markedRelation_of_nativeRelation {m : ℕ} (u v : SL2 × (Fin m → X))
    (h : NativeRelation q u v) :
    (markedRelation (Z := Fin m → X) (NativeAffineGroup.derivative q)).r u v := by
  obtain ⟨e, he⟩ := h
  let φ := conjugateAffine q e
  let a : NativeAffineGroup.AffineGroup q := ⟨NativeAffineGroup.asRaw φ, u.1⁻¹ * v.1, φ, rfl⟩
  refine ⟨a, ?_, ?_⟩
  · change v.1 = u.1 * (u.1⁻¹ * v.1)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  · funext i
    change v.2 i = φ.surface.symm (u.2 i)
    apply φ.surface.injective
    rw [Homeomorph.apply_symm_apply]
    change (toOriginal q u.1) (e.homeomorph ((toOriginal q v.1).symm (v.2 i))) = u.2 i
    have hmark := congrArg (toOriginal q u.1) (he i)
    simpa only [Homeomorph.apply_symm_apply] using hmark

theorem markedRelation_iff_nativeRelation {m : ℕ} (u v : SL2 × (Fin m → X)) :
    (markedRelation (Z := Fin m → X) (NativeAffineGroup.derivative q)).r u v ↔ NativeRelation q u v :=
  ⟨nativeRelation_of_markedRelation q u v, markedRelation_of_nativeRelation q u v⟩

theorem markedClass_eq_iff_nativeRelation {m : ℕ} (u v : SL2 × (Fin m → X)) :
    markedClass (NativeAffineGroup.derivative q) u = markedClass (NativeAffineGroup.derivative q) v ↔
      NativeRelation q u v := by
  change Quotient.mk (markedRelation (NativeAffineGroup.derivative q)) u =
      Quotient.mk (markedRelation (NativeAffineGroup.derivative q)) v ↔ _
  exact Quotient.eq.trans (markedRelation_iff_nativeRelation q u v)

theorem configurationClass_eq_iff_nativeRelation {m : ℕ}
    (u v : SL2 × ConfigurationSpace m X) :
    markedClass (NativeAffineGroup.derivative q) u = markedClass (NativeAffineGroup.derivative q) v ↔
      NativeRelation q (u.1, u.2.val) (v.1, v.2.val) := by
  change Quotient.mk (markedRelation (NativeAffineGroup.derivative q)) u =
      Quotient.mk (markedRelation (NativeAffineGroup.derivative q)) v ↔ _
  rw [Quotient.eq]
  apply Iff.trans ?_ (markedRelation_iff_nativeRelation q (u.1, u.2.val) (v.1, v.2.val))
  constructor
  · rintro ⟨a, hA, hb⟩
    exact ⟨a, hA, congrArg Subtype.val hb⟩
  · rintro ⟨a, hA, hb⟩
    exact ⟨a, hA, Subtype.ext hb⟩

end VeechDichotomy.NativeMarkedOrbitEquivalence
