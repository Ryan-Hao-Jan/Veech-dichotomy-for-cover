module

public import VeechDichotomy.BeltramiMarkedFlatFlow

/-! Actual native vertical flows converge in fixed persistent flat
rectangles. Common lifetimes and the convergence of their actual total
inclusions follow from the constructed coordinates and native flow
uniqueness, rather than a supplied convergence-of-flows premise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFlowConvergence

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativePrimitiveRectangles
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem vertical_flow_limit {J : Type*} {l : Filter J}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) (x₀ : Regular (fiberForm π F hBranch p₀))
    (hx₀ : x₀.val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {W H : ℝ} (hH : 0 < H)
    (hR : ∀ v ∈ Icc (-W) W ×ˢ Icc (-H) H, toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hinner : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀.val) ∈ rectangle (-W) W (-(H / 2)) (H / 2))
    {p : J → Base A} (x : ∀ j, Regular (fiberForm π F hBranch (p j)))
    (hpoints : Tendsto (fun j => inclusion π F hBranch (p j) (x j).val) l (𝓝 (inclusion π F hBranch p₀ x₀.val)))
    {t : J → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-(H / 2)) (H / 2)) (ht : Tendsto t l (𝓝 t₀)) :
    (∀ᶠ j in l, Ioo (-(H / 2)) (H / 2) ⊆ domain (fiberForm π F hBranch (p j)) vertical (x j)) ∧
      Tendsto (fun j => inclusion π F hBranch (p j) (trajectory (fiberForm π F hBranch (p j)) vertical (x j) (t j)).val)
        l (𝓝 (inclusion π F hBranch p₀ (trajectory (fiberForm π F hBranch p₀) vertical x₀ t₀).val)) := by
  let u₀ := inclusion π F hBranch p₀ x₀.val
  let u := fun j => inclusion π F hBranch (p j) (x j).val
  have hsource : u₀ ∈ source π F hBranch s := hx₀
  have hc := coordinate_tendsto π F hBranch s hsource hpoints
  have hp : Tendsto p l (𝓝 p₀) := by
    simpa only [Function.comp_def, projection_inclusion] using
      (projection_holomorphic π F hBranch).continuous.continuousAt.tendsto.comp hpoints
  let K : Set ℂ := toPlane.symm '' (Icc (-W) W ×ˢ Icc (-H) H)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image toPlane.symm.continuous
  have hKsub : K ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target := by
    rintro _ ⟨v, hv, rfl⟩
    exact hR v hv
  obtain ⟨U, hU, hpU, hUK⟩ := BeltramiMarkedUniformSlices.compact_persistence π F hBranch s p₀ hK hKsub
  have hopenInner : IsOpen (rectangle (-W) W (-(H / 2)) (H / 2)) := isOpen_Ioo.prod isOpen_Ioo
  have hlate : ∀ᶠ j in l,
      Ioo (-(H / 2)) (H / 2) ⊆ domain (fiberForm π F hBranch (p j)) vertical (x j) ∧
        inclusion π F hBranch (p j) (trajectory (fiberForm π F hBranch (p j)) vertical (x j) (t j)).val =
          BeltramiMarkedUniformSlices.inverse π F hBranch s
            (p j, toPlane.symm (coordinate π F hBranch s (u j) + t j • vertical)) := by
    filter_upwards [eventually_source π F hBranch s hsource hpoints,
      hc (hopenInner.mem_nhds hinner), hp (hU.mem_nhds hpU), ht (isOpen_Ioo.mem_nhds ht₀)] with j hjS hjR hjU hjT
    have hxj : (x j).val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s (p j)).source := hjS
    have hRj : ∀ v ∈ rectangle (-W) W (-H) H,
        toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s (p j)).target := by
      intro v hv
      exact hUK (p j) hjU ⟨v, ⟨⟨hv.1.1.le, hv.1.2.le⟩, ⟨hv.2.1.le, hv.2.2.le⟩⟩, rfl⟩
    have hflow := BeltramiMarkedFlatFlow.uniform_vertical_time π F hBranch s hs hreg (p j)
      (BeltramiMarkedScaledSlices.chart π F hBranch s (p j) (x j).val)
      ((BeltramiMarkedScaledSlices.chart π F hBranch s (p j)).map_source hxj) hH hRj (x j) hxj hjR
    exact ⟨hflow.1, hflow.2 (t j) hjT⟩
  have hline₀ : toPlane.symm (coordinate π F hBranch s u₀ + t₀ • vertical) ∈
      (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target := by
    apply hR
    rw [add_vertical]
    exact ⟨⟨hinner.1.1.le, hinner.1.2.le⟩,
      by constructor <;> linarith [hinner.2.1, hinner.2.2, ht₀.1, ht₀.2]⟩
  have hline : Tendsto (fun j => toPlane.symm (coordinate π F hBranch s (u j) + t j • vertical)) l
      (𝓝 (toPlane.symm (coordinate π F hBranch s u₀ + t₀ • vertical))) :=
    toPlane.symm.continuous.continuousAt.tendsto.comp (hc.add (ht.smul tendsto_const_nhds))
  have hInv := BeltramiMarkedUniformSlices.inverse_tendsto π F hBranch s p₀ hline₀ (hp.prodMk_nhds hline)
  have hactual := Tendsto.congr' (hl := hlate.mono (fun _ hj => hj.2.symm)) hInv
  have hR₀ : ∀ v ∈ rectangle (-W) W (-H) H, toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target :=
    fun v hv => hR v ⟨⟨hv.1.1.le, hv.1.2.le⟩, ⟨hv.2.1.le, hv.2.2.le⟩⟩
  have hflow₀ := BeltramiMarkedFlatFlow.uniform_vertical_time π F hBranch s hs hreg p₀
    (BeltramiMarkedScaledSlices.chart π F hBranch s p₀ x₀.val)
    ((BeltramiMarkedScaledSlices.chart π F hBranch s p₀).map_source hx₀) hH hR₀ x₀ hx₀ hinner
  refine ⟨hlate.mono (fun _ hj => hj.1), ?_⟩
  rw [hflow₀.2 t₀ ht₀]
  exact hactual

end VeechDichotomy.BeltramiMarkedFlowConvergence
