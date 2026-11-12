module

public import VeechDichotomy.NativeCoverFlow
public import Mathlib.Topology.Covering.Basic

/-! Away from the branch values and zeros of the base differential, the
actual holomorphic translation cover is an ordinary finite covering map.
Local triviality is derived from the proved local translation formula.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeUnramifiedCover

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover NativeCoverFlow Set Filter Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

theorem isLocalHomeomorph_regularMap (π : Cover ωX ωY) :
    IsLocalHomeomorph (regularMap π) := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  apply IsLocalHomeomorphOn.mk
  intro y _
  obtain ⟨a, htarget, hfactor⟩ := translation_factor_germ π y
  let A := coordinateChart ωY y
  let B := coordinateChart ωX (regularMap π y)
  let e := (A.transHomeomorph (Homeomorph.addRight a)).trans B.symm
  have hy : y ∈ e.source := ⟨coordinateChart_center ωY y, htarget⟩
  have hnear : ∀ᶠ z in 𝓝 y, z ∈ e.source ∧ regularMap π z = e z := by
    filter_upwards [e.open_source.mem_nhds hy, hfactor] with z hz heq
    exact ⟨hz, heq⟩
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hnear
  refine ⟨e.restr U, ⟨hy, ?_⟩, ?_⟩
  · rwa [hU.interior_eq]
  · intro z hz
    exact (hUsub (interior_subset hz.2)).2

theorem isLocalHomeomorphOn_regular (π : Cover ωX ωY) :
    IsLocalHomeomorphOn π.map (regularSet ωY) := by
  have hY := (regularSet_open ωY).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hX := (regularSet_open ωX).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph (π.map ∘ (Subtype.val : Regular ωY → Y)) :=
    hX.comp (isLocalHomeomorph_regularMap π)
  have h := IsLocalHomeomorphOn.of_comp_right (s := (univ : Set (Regular ωY)))
    hcomp.isLocalHomeomorphOn hY.isLocalHomeomorphOn
  simpa only [image_univ, Subtype.range_coe] using h

/-- A nonzero complex linear endomorphism of a complex line is injective. -/
theorem complexLine_injective_of_ne_zero (f : ℂ →L[ℂ] ℂ) (hf : f ≠ 0) :
    Function.Injective f := by
  have hrep : ∀ z : ℂ, f z = z * f 1 := by
    intro z
    have h := f.map_smul z (1 : ℂ)
    simpa only [smul_eq_mul, mul_one] using h
  have h1 : f 1 ≠ 0 := by
    intro hz
    apply hf
    apply ContinuousLinearMap.ext
    intro z
    simp only [hrep z, hz, mul_zero, zero_apply]
  intro z w hzw
  exact mul_right_cancel₀ h1 (by simpa only [← hrep] using hzw)

theorem regular_of_regular_image_and_noncritical (π : Cover ωX ωY) {y : Y}
    (hx : π.map y ∈ regularSet ωX)
    (hcrit : y ∉ criticalSet π) : y ∈ regularSet ωY := by
  have hinj : Function.Injective (ωX.val.toFun (π.map y)) :=
    complexLine_injective_of_ne_zero _ hx
  intro hy
  apply hcrit
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y = 0
  apply ContinuousLinearMap.ext
  intro z
  apply hinj
  have hcomp := (pullback_at π y).symm.trans hy
  have h := congrArg (fun f => f z) hcomp
  simpa only [ContinuousLinearMap.comp_apply, zero_apply,
    map_zero] using h

def unramifiedRegularBase (π : Cover ωX ωY) : Set X :=
  regularSet ωX \ branchValues π

theorem unramifiedRegularBase_open (π : Cover ωX ωY) :
    IsOpen (unramifiedRegularBase π) :=
  (regularSet_open ωX).sdiff (branchValues_closed π)

theorem preimage_unramifiedRegularBase_subset (π : Cover ωX ωY) :
    π.map ⁻¹' unramifiedRegularBase π ⊆ regularSet ωY := by
  intro y hy
  apply regular_of_regular_image_and_noncritical π hy.1
  intro hcrit
  exact hy.2 ⟨y, hcrit, rfl⟩

theorem isCoveringMapOn_unramifiedRegularBase (π : Cover ωX ωY) :
    IsCoveringMapOn π.map (unramifiedRegularBase π) :=
  (NativeTranslationCover.isProperMap π).isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun x _ => π.finite_fibers x)
    ((isLocalHomeomorphOn_regular π).mono (preimage_unramifiedRegularBase_subset π))

end VeechDichotomy.NativeUnramifiedCover
