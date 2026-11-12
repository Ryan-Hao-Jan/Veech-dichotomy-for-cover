module

public import VeechDichotomy.BeltramiMarkedFiberEmbeddings
public import VeechDichotomy.NativeDifferentialScale

/-! Nonzero scalar extension of the actual simultaneous marked family.
The complex source family remains a genuine proper holomorphic submersion;
its fiber differentials and finite covers are actual scalar multiples.
No global total-space one-form on the varying base is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedScaledFamily

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

abbrev Base (A : Data qX b μ₀) := NonzeroComplexParameter.Parameter × ComplexBeltramiMarkParameters.Parameters A
abbrev Total := NonzeroComplexParameter.Parameter × BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch
abbrev BaseTotal (A : Data qX b μ₀) := NonzeroComplexParameter.Parameter × BeltramiMarkedReferenceSpace.TotalSpace A qX

def projection (z : Total π F hBranch) : Base A :=
  (z.1, BeltramiMarkedCoverTotalSpace.projection π F hBranch z.2)

theorem proper_projection : IsProperMap (projection π F hBranch) :=
  isProperMap_id.prodMap (BeltramiMarkedCoverTotalSpace.proper_projection π F hBranch)

theorem projection_holomorphic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))) ω (projection π F hBranch) :=
  contMDiff_id.prodMap (BeltramiMarkedCoverTotalSpace.projection_holomorphic π F hBranch)

theorem projection_surjective_derivative (z : Total π F hBranch) :
    Function.Surjective (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))) (projection π F hBranch) z) := by
  have hi : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (id : NonzeroComplexParameter.Parameter → NonzeroComplexParameter.Parameter) z.1 :=
    mdifferentiableAt_id
  have hp := (BeltramiMarkedCoverTotalSpace.projection_holomorphic π F hBranch).mdifferentiableAt (by decide) (x := z.2)
  change Function.Surjective (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)))
      (Prod.map id (BeltramiMarkedCoverTotalSpace.projection π F hBranch)) z)
  rw [mfderiv_prodMap hi hp, mfderiv_id]
  intro v
  obtain ⟨w, hw⟩ := BeltramiMarkedCoverTotalSpace.projection_surjective_derivative π F hBranch z.2 v.2
  exact ⟨(v.1, w), Prod.ext rfl hw⟩

def fiberForm (p : Base A) : Differential (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :=
  NativeDifferentialScale.form p.1 (BeltramiMarkedFiberDifferential.form π F hBranch p.2)

def baseFiberForm (p : Base A) : Differential (NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A p.2)) :=
  NativeDifferentialScale.form p.1 (NativeBeltramiDifferential.form qX (BeltramiMarkedReferenceCharts.parameter A p.2))

def cover (p : Base A) : Cover (baseFiberForm p) (fiberForm π F hBranch p) :=
  NativeDifferentialScale.cover p.1 (BeltramiMarkedFiberDifferential.cover π F hBranch p.2)

def inclusion (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) : Total π F hBranch :=
  (p.1, BeltramiMarkedFiberSurface.inclusion π F hBranch p.2 y)

theorem projection_inclusion (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    projection π F hBranch (inclusion π F hBranch p y) = p := rfl

theorem holomorphic_inclusion (p : Base A) : ContMDiff 𝓘(ℂ)
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) ω (inclusion π F hBranch p) :=
  contMDiff_const.prodMk (BeltramiMarkedFiberSurface.holomorphic_inclusion π F hBranch p.2)

def fiberHomeomorph (p : Base A) : BeltramiMarkedFiberSurface.Surface π F hBranch p.2 ≃ₜ (projection π F hBranch ⁻¹' {p}) where
  toFun y := ⟨inclusion π F hBranch p y, rfl⟩
  invFun y := (BeltramiMarkedFiberSurface.toOriginal π F hBranch p.2).symm
    (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch y.val.2).2
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact (congrArg Prod.fst y.property).symm
    · apply (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).injective
      exact Prod.ext (congrArg Prod.snd y.property).symm rfl
  continuous_toFun := (continuous_const.prodMk (BeltramiMarkedFiberSurface.continuous_inclusion π F hBranch p.2)).subtype_mk _
  continuous_invFun := (BeltramiMarkedFiberSurface.toOriginal π F hBranch p.2).symm.continuous.comp
    (continuous_snd.comp ((BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).continuous.comp
      (continuous_snd.comp continuous_subtype_val)))

def map (z : Total π F hBranch) : BaseTotal A := (z.1, BeltramiMarkedCoverTotalSpace.map π F hBranch z.2)

theorem holomorphic_map : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
    (𝓘(ℂ).prod 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) ω (map π F hBranch) :=
  contMDiff_id.prodMap (BeltramiMarkedCoverTotalSpace.holomorphic_map π F hBranch)

theorem proper_map : IsProperMap (map π F hBranch) :=
  isProperMap_id.prodMap (BeltramiMarkedCoverFiniteMap.proper_map π F hBranch)

theorem surjective_map : Function.Surjective (map π F hBranch) := by
  intro x
  obtain ⟨y, hy⟩ := BeltramiMarkedCoverFiniteMap.surjective_map π F hBranch x.2
  exact ⟨(x.1, y), Prod.ext rfl hy⟩

theorem finite_fibers (x : BaseTotal A) : (map π F hBranch ⁻¹' {x}).Finite := by
  apply ((BeltramiMarkedCoverFiniteMap.finite_fibers π F hBranch x.2).image (fun y => (x.1, y))).subset
  intro y hy
  exact ⟨y.2, congrArg Prod.snd hy, Prod.ext (congrArg Prod.fst hy).symm rfl⟩

theorem degree_eq (p : Base A) : NativeFullCoverDegree.degree (cover π F hBranch p) = NativeFullCoverDegree.degree π :=
  (NativeDifferentialScale.degree_eq p.1 (BeltramiMarkedFiberDifferential.cover π F hBranch p.2)).trans
    (BeltramiMarkedFiberBranchValues.degree_eq π F hBranch p.2)

end VeechDichotomy.BeltramiMarkedScaledFamily
