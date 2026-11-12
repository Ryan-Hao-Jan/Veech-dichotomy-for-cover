module

public import VeechDichotomy.HolomorphicCotangentForms

/-! Local frame coefficients of an actual holomorphic cotangent section
vary holomorphically on its chart neighborhood, in arbitrary complex
model dimension. This applies to vertical coefficients of analytic families. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCotangentCoefficients

open HolomorphicCotangentForms Set Filter Topology Bundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

abbrev frame (center : M) := trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := M)) center

def coefficient (α : Form E M) (center : M) (v : E) (x : M) : ℂ :=
  α.toFun x ((frame (E := E) center).symmL ℂ x v)

theorem frame_section_contMDiffAt (center : M) (v : E) {x : M} (hx : x ∈ (frame (E := E) center).baseSet) :
    ContMDiffAt 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω
      (fun y => TotalSpace.mk' E y ((frame (E := E) center).symmL ℂ y v)) x := by
  let e := frame (E := E) center
  have ht : (x, v) ∈ e.target := by rw [e.target_eq]; exact ⟨hx, mem_univ v⟩
  have hInv : ContMDiffAt (𝓘(ℂ, E).prod 𝓘(ℂ, E)) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω
      e.toOpenPartialHomeomorph.symm (x, v) :=
    e.contMDiffOn_symm.contMDiffAt (e.toOpenPartialHomeomorph.open_target.mem_nhds ht)
  have hpair : ContMDiffAt 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω (fun y : M => (y, v)) x :=
    contMDiffAt_id.prodMk contMDiffAt_const
  apply (hInv.comp x hpair).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  change TotalSpace.mk' E y (e.symmL ℂ y v) = e.toOpenPartialHomeomorph.symm (y, v)
  simpa only [Trivialization.symmL_apply e hy, Function.comp_apply] using! Trivialization.mk_symm e hy v

theorem coefficient_contMDiffAt (α : Form E M) (center : M) (v : E) {x : M}
    (hx : x ∈ (frame (E := E) center).baseSet) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω (coefficient α center v) x := by
  have hv := frame_section_contMDiffAt (E := E) center v hx
  have happ := (α.contMDiff_toFun x).clm_bundle_apply hv
  have hc := (contMDiffAt_totalSpace.mp happ).2
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω (fun y => α.toFun y ((frame (E := E) center).symmL ℂ y v)) x
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply] using! hc

theorem coefficient_holomorphic (α : Form E M) (center : M) (v : E) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ) ω (coefficient α center v) (frame (E := E) center).baseSet :=
  fun _ hx => (coefficient_contMDiffAt α center v hx).contMDiffWithinAt

theorem coefficient_continuousOn (α : Form E M) (center : M) (v : E) :
    ContinuousOn (coefficient α center v) (frame (E := E) center).baseSet :=
  (coefficient_holomorphic α center v).continuousOn

end VeechDichotomy.HolomorphicCotangentCoefficients
