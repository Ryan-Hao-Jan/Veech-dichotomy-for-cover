module

public import VeechDichotomy.NativeCoverBranchTopology
public import VeechDichotomy.NativeCoverDegree
public import Jacobians.Surface.ManifoldIFT

/-! The genuine native cover is an ordinary covering over the complement
of its actual branch values, including points where the base form vanishes.
Both punctured curves are path connected and the fibers are finite. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePuncturedCover

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeCoverBranchTopology
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

theorem isLocalHomeomorphOn_noncritical (π : Cover ωX ωY) :
    IsLocalHomeomorphOn π.map (criticalSet π)ᶜ := by
  apply IsLocalHomeomorphOn.mk
  intro y hy
  let c := chartAt ℂ y
  let d := chartAt ℂ (π.map y)
  let F : ℂ → ℂ := d ∘ π.map ∘ c.symm
  have hc : y ∈ c.source := mem_chart_source ℂ y
  have hd : π.map y ∈ d.source := mem_chart_source ℂ (π.map y)
  have ha : AnalyticAt ℂ F (c y) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback π.holomorphic y
  have hder : deriv F (c y) ≠ 0 := by
    intro hz
    apply hy
    change mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y = 0
    rw [mfderiv_eq_fderiv_chart]
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℂ F (c y) z = 0
    rw [fderiv_eq_smul_deriv, hz, smul_zero]
  have hs := ha.hasStrictDerivAt.hasStrictFDerivAt_equiv hder
  let C : OpenPartialHomeomorph ℂ ℂ := hs.toOpenPartialHomeomorph F
  have hCs : c y ∈ C.source := hs.mem_toOpenPartialHomeomorph_source
  have hCf : (C : ℂ → ℂ) = F := hs.toOpenPartialHomeomorph_coe
  have hval : C (c y) = d (π.map y) := by
    rw [hCf]
    change d (π.map (c.symm (c y))) = _
    rw [c.left_inv hc]
  let e := (c.trans C).trans d.symm
  let V := π.map ⁻¹' d.source
  have hV : IsOpen V := d.open_source.preimage π.holomorphic.continuous
  have hyV : y ∈ V := hd
  have hye : y ∈ e.source := ⟨⟨hc, hCs⟩, by
    change C (c y) ∈ d.target
    rw [hval]
    exact d.map_source hd⟩
  refine ⟨e.restr V, ⟨hye, by rwa [hV.interior_eq]⟩, ?_⟩
  intro z hz
  have hzc : z ∈ c.source := hz.1.1.1
  have hzV : z ∈ V := interior_subset hz.2
  have hzd : π.map z ∈ d.source := hzV
  change π.map z = d.symm (C (c z))
  rw [hCf]
  change π.map z = d.symm (d (π.map (c.symm (c z))))
  rw [c.left_inv hzc, d.left_inv hzd]

def base (π : Cover ωX ωY) : Set X := (branchValues π)ᶜ

def source (π : Cover ωX ωY) : Set Y := π.map ⁻¹' base π

theorem source_subset_noncritical (π : Cover ωX ωY) : source π ⊆ (criticalSet π)ᶜ := by
  intro y hy hc
  exact hy ⟨y, hc, rfl⟩

theorem isCoveringMapOn_base (π : Cover ωX ωY) : IsCoveringMapOn π.map (base π) :=
  (NativeTranslationCover.isProperMap π).isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun x _ => π.finite_fibers x)
    ((isLocalHomeomorphOn_noncritical π).mono (source_subset_noncritical π))

def puncturedMap (π : Cover ωX ωY) : source π → base π := (base π).restrictPreimage π.map

theorem isCoveringMap_puncturedMap (π : Cover ωX ωY) : IsCoveringMap (puncturedMap π) :=
  (isCoveringMapOn_base π).isCoveringMap_restrictPreimage

theorem preimage_branchValues_finite (π : Cover ωX ωY) : (π.map ⁻¹' branchValues π).Finite := by
  have heq : π.map ⁻¹' branchValues π = ⋃ x ∈ branchValues π, π.map ⁻¹' {x} := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    exact ⟨fun hy => ⟨π.map y, hy, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ hx⟩
  rw [heq]
  exact (branchValues_finite π).biUnion fun x _ => π.finite_fibers x

theorem base_pathConnected (π : Cover ωX ωY) : IsPathConnected (base π) := by
  let : Infinite X := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := (branchValues_finite π).exists_notMem
  exact Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
    (branchValues_finite π) ⟨x, hx⟩

theorem source_pathConnected (π : Cover ωX ωY) : IsPathConnected (source π) := by
  let : Infinite Y := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hfin := preimage_branchValues_finite π
  obtain ⟨y, hy⟩ := hfin.exists_notMem
  exact Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
    hfin ⟨y, hy⟩

theorem puncturedMap_surjective (π : Cover ωX ωY) : Function.Surjective (puncturedMap π) := by
  intro x
  obtain ⟨y, hy⟩ := π.surjective x.val
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change π.map y ∈ base π
  rw [hy]
  exact x.property

def fiberEquiv (π : Cover ωX ωY) (x : base π) :
    (puncturedMap π ⁻¹' {x}) ≃ (π.map ⁻¹' {x.val}) where
  toFun y := ⟨y.val.val, congrArg Subtype.val y.property⟩
  invFun y := ⟨⟨y.val, by
    change π.map y.val ∈ base π
    rw [y.property]
    exact x.property⟩, Subtype.ext y.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem fiber_finite (π : Cover ωX ωY) (x : base π) : Finite (puncturedMap π ⁻¹' {x}) := by
  let : Finite (π.map ⁻¹' {x.val}) := (π.finite_fibers x.val).to_subtype
  exact Finite.of_equiv _ (fiberEquiv π x).symm

theorem fiber_card_eq (π : Cover ωX ωY) (x : base π) :
    Nat.card (puncturedMap π ⁻¹' {x}) = Nat.card (π.map ⁻¹' {x.val}) :=
  Nat.card_congr (fiberEquiv π x)

end VeechDichotomy.NativePuncturedCover
