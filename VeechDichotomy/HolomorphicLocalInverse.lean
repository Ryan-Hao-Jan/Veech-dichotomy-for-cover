module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Analysis.Complex.Basic

/-! A genuine local homeomorphism of complex curves has a holomorphic
inverse wherever its actual forward complex derivative is nonzero.
This generalizes the supplied native primitive-inverse calculation.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicLocalInverse

open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {Y X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω X] in
theorem mfderiv_eq_fderiv_chart {f : Y → X} {y : Y}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f y =
      fderiv ℂ ((chartAt ℂ (f y)) ∘ f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) := by
  rw [hf.mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ]

theorem mdifferentiableAt_symm (e : OpenPartialHomeomorph Y X) {y : Y}
    (hy : y ∈ e.source) (he : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e y)
    (hder : mfderiv 𝓘(ℂ) 𝓘(ℂ) e y ≠ 0) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (e y) := by
  let c := chartAt ℂ y
  let d := chartAt ℂ (e y)
  let F := (c.symm.trans e).trans d
  have hyc : y ∈ c.source := mem_chart_source ℂ y
  have hyd : e y ∈ d.source := mem_chart_source ℂ (e y)
  have hcT : c y ∈ c.target := c.map_source hyc
  have hFsrc : c y ∈ F.source := by
    change (c y ∈ c.target ∧ c.symm (c y) ∈ e.source) ∧ e (c.symm (c y)) ∈ d.source
    rw [c.left_inv hyc]
    exact ⟨⟨hcT, hy⟩, hyd⟩
  have hFvalue : F (c y) = d (e y) := by
    change d (e (c.symm (c y))) = _
    rw [c.left_inv hyc]
  have hcInv := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ y) hcT
  have he' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e (c.symm (c y)) := by rw [c.left_inv hyc]; exact he
  have hd' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) d (e (c.symm (c y))) := by
    rw [c.left_inv hyc]
    exact mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (e y)) hyd
  have hFD : DifferentiableAt ℂ F (c y) :=
    ((hd'.comp (c y) (he'.comp (c y) hcInv)).hasMFDerivAt.hasFDerivAt).differentiableAt
  have hscalar : deriv F (c y) ≠ 0 := by
    intro hz
    apply hder
    rw [mfderiv_eq_fderiv_chart he]
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℂ F (c y) z = 0
    rw [fderiv_eq_smul_deriv, hz, smul_zero]
  have hFt : d (e y) ∈ F.target := hFvalue ▸ F.map_source hFsrc
  have hFInv : F.symm (d (e y)) = c y := by rw [← hFvalue]; exact F.left_inv hFsrc
  have hInvD := F.hasDerivAt_symm hFt hscalar (by rw [hFInv]; exact hFD.hasDerivAt)
  have hcInv' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (F.symm (d (e y))) := by
    rw [hFInv]
    exact hcInv
  have hd := mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (e y)) hyd
  have hcomp := hcInv'.comp (e y) (hInvD.differentiableAt.mdifferentiableAt.comp (e y) hd)
  have hnearC : ∀ᶠ x in 𝓝 (e y), e.symm x ∈ c.source := by
    have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
      simpa only [e.left_inv hy] using (e.symm.continuousAt (e.map_source hy)).tendsto
    exact ht (c.open_source.mem_nhds hyc)
  have hfactor : (e.symm : X → Y) =ᶠ[𝓝 (e y)] fun x => c.symm (F.symm (d x)) := by
    filter_upwards [d.open_source.mem_nhds hyd, hnearC] with x hxD hxC
    change e.symm x = c.symm (c (e.symm (d.symm (d x))))
    rw [d.left_inv hxD, c.left_inv hxC]
  exact hcomp.congr_of_eventuallyEq hfactor

theorem mdifferentiable (e : OpenPartialHomeomorph Y X)
    (he : ∀ y ∈ e.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e y)
    (hder : ∀ y ∈ e.source, mfderiv 𝓘(ℂ) 𝓘(ℂ) e y ≠ 0) : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · exact fun y hy => (he y hy).mdifferentiableWithinAt
  · intro x hx
    have h := mdifferentiableAt_symm e (e.map_target hx) (he _ (e.map_target hx)) (hder _ (e.map_target hx))
    simpa only [e.right_inv hx] using h.mdifferentiableWithinAt

end VeechDichotomy.HolomorphicLocalInverse
