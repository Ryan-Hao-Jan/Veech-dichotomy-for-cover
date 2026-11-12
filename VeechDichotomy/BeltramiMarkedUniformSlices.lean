module

public import VeechDichotomy.BeltramiMarkedScaledSlices
public import VeechDichotomy.CompactFiberTubes

/-! Actual inverses of fixed scalar-extended fiber charts vary jointly
continuously in the proper total family. Any compact flat region in a
limit chart persists on all nearby fibers, with its prescribed total
neighborhood. No varying-chart compactness premise is an input. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedUniformSlices

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def coordinateInput (t : Base A × ℂ) : ComplexBeltramiMarkParameters.Space (m := m) × ℂ :=
  (t.1.2.val, t.1.1.val⁻¹ * t.2)

theorem continuous_coordinateInput : Continuous (coordinateInput (A := A)) :=
  ((continuous_subtype_val.comp continuous_snd).comp continuous_fst).prodMk
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).inv₀
      (fun t => t.1.1.property)).mul continuous_snd)

def domain (s : ComplexBeltramiMarkParameters.Parameters A × Y) : Set (Base A × ℂ) :=
  coordinateInput ⁻¹' (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).target

theorem domain_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) : IsOpen (domain π F hBranch s) :=
  (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).open_target.preimage continuous_coordinateInput

theorem mem_domain (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) (z : ℂ) :
    (p, z) ∈ domain π F hBranch s ↔ z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target := Iff.rfl

def inverse (s : ComplexBeltramiMarkParameters.Parameters A × Y) (t : Base A × ℂ) : Total π F hBranch :=
  (t.1.1, (BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).symm (coordinateInput t))

theorem continuousOn_inverse (s : ComplexBeltramiMarkParameters.Parameters A × Y) :
    ContinuousOn (inverse π F hBranch s) (domain π F hBranch s) :=
  (continuous_fst.comp continuous_fst).continuousOn.prodMk
    ((BeltramiMarkedCoverCoordinates.sourceChart π F hBranch s).symm.continuousOn.comp
      continuous_coordinateInput.continuousOn (fun _ ht => ht))

theorem inverse_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) {z : ℂ}
    (hz : z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    inverse π F hBranch s (p, z) = inclusion π F hBranch p ((BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z) := by
  exact congrArg (fun y => (p.1, y))
    (BeltramiMarkedCoverCoordinates.source_inverse_value π F hBranch s p.2 hz)

theorem compact_persistence (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    ∃ U : Set (Base A), IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s q).target :=
  CompactFiberTubes.exists_open_tube (domain_open π F hBranch s) p hK hsub

theorem compact_persistence_in (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    {W : Set (Total π F hBranch)} (hW : IsOpen W)
    (hKW : ∀ z ∈ K, inverse π F hBranch s (p, z) ∈ W) :
    ∃ U : Set (Base A), IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, ∀ z ∈ K,
      z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s q).target ∧ inverse π F hBranch s (q, z) ∈ W := by
  have hopen : IsOpen (domain π F hBranch s ∩ inverse π F hBranch s ⁻¹' W) :=
    (continuousOn_inverse π F hBranch s).isOpen_inter_preimage (domain_open π F hBranch s) hW
  exact CompactFiberTubes.exists_open_tube hopen p hK (fun z hz => ⟨hsub hz, hKW z hz⟩)

theorem inverse_tendsto {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) {z : ℂ}
    (hz : z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    {f : I → Base A × ℂ} (hf : Tendsto f l (𝓝 (p, z))) :
    Tendsto (fun i => inverse π F hBranch s (f i)) l (𝓝 (inverse π F hBranch s (p, z))) :=
  ((continuousOn_inverse π F hBranch s).continuousAt ((domain_open π F hBranch s).mem_nhds hz)).tendsto.comp hf

end VeechDichotomy.BeltramiMarkedUniformSlices
