module

public import VeechDichotomy.UniformBeltramiMarkTransport
public import VeechDichotomy.ComplexBeltramiMarkParameters
public import VeechDichotomy.NormalizedBeltramiTotalInverse

/-! The actual moved marks are jointly holomorphic sections over the
open complex domain of structure and displacement parameters. The proof
identifies the constructed whole-surface transport with one total chart
inverse, including at zeros. Distinctness follows from the actual homeomorphism. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiMarkSections

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} {A : Data q b μ₀} (F : Family A)

def sectionMap (i : Fin m) (a : ComplexBeltramiMarkParameters.Parameters A) : NativeBeltramiTotalSpace.TotalSpace q :=
  let p := ComplexBeltramiMarkParameters.productHomeomorph A a
  ⟨(p.1.val, F.map p (b i))⟩

theorem section_formula (i : Fin m) (a : ComplexBeltramiMarkParameters.Parameters A) :
    sectionMap F i a = NormalizedBeltramiTotalInverse.inverse (A.disks i) (a.val.1, a.val.2 i) := by
  let p := ComplexBeltramiMarkParameters.productHomeomorph A a
  have h := NormalizedBeltramiTotalInverse.inverse_value (A.disks i) (A.localBase p.1 i) (p.2 i).val
  change NormalizedBeltramiTotalInverse.inverse (A.disks i) (p.1.val.val, (p.2 i).val) = _ at h
  change sectionMap F i a = NormalizedBeltramiTotalInverse.inverse (A.disks i) (p.1.val.val, (p.2 i).val)
  rw [h]
  apply (NativeBeltramiTotalSpace.toProduct q).injective
  refine Prod.ext rfl ?_
  exact congrArg NativeBeltramiSurface.Surface.point (F.moves p i)

theorem holomorphic_section (i : Fin m) :
    ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) 𝓘(ℂ, ℂ × ℂ) ω (sectionMap F i) := by
  intro a
  let p := ComplexBeltramiMarkParameters.productHomeomorph A a
  have hz : ‖(p.2 i).val‖ ≤ 2 := by
    have hi := (p.2 i).property
    linarith
  have hInv := NormalizedBeltramiTotalInverse.uniform_holomorphicAt
    (A.disks i) (A.localBase p.1 i) hz
  have hcoord : ContDiff ℂ ω (fun z : ComplexBeltramiMarkParameters.Space (m := m) => (z.1, z.2 i)) :=
    contDiff_fst.prodMk ((ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).contDiff.comp contDiff_snd)
  have hinput : ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) 𝓘(ℂ, ℂ × ℂ) ω
      (fun a : ComplexBeltramiMarkParameters.Parameters A => (a.val.1, a.val.2 i)) a :=
    (hcoord.contMDiff a.val).comp a (ComplexBeltramiMarkParameters.inclusion_holomorphic A a)
  apply (hInv.comp a hinput).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (section_formula F i)

theorem projection_section (i : Fin m) (a : ComplexBeltramiMarkParameters.Parameters A) :
    NativeBeltramiTotalSpace.projection q (sectionMap F i a) =
      (ComplexBeltramiMarkParameters.productHomeomorph A a).1.val := rfl

theorem distinct_sections (a : ComplexBeltramiMarkParameters.Parameters A) :
    Function.Injective (fun i => sectionMap F i a) := by
  intro i j hij
  apply A.injective
  apply (F.map (ComplexBeltramiMarkParameters.productHomeomorph A a)).injective
  exact congrArg (fun x : NativeBeltramiTotalSpace.TotalSpace q => x.point.2) hij

end VeechDichotomy.UniformBeltramiMarkSections
