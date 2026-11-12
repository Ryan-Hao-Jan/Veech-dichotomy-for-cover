module

public import VeechDichotomy.NativeMovingCoverRegularity
public import VeechDichotomy.ComplexAtlasTools

/-! Actual raw complex charts for a cover with moved branch values.
Regular charts are pulled back from the base through genuine local
homeomorphisms. At critical points, restricted original native charts
are used on the proved holomorphic neighborhoods. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Filter Topology
open scoped Manifold ContDiff Classical

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

abbrev RegularPoint (π : Cover ωX ωY) := ↥(criticalSet π)ᶜ
abbrev CriticalPoint (π : Cover ωX ωY) := ↥(criticalSet π)

abbrev projection (π : Cover ωX ωY) (ψ : X ≃ₜ X) := NativeMovingCoverMap.map π ψ

def oldLocalMap (π : Cover ωX ωY) (y : RegularPoint π) :
    OpenPartialHomeomorph Y X :=
  Classical.choose (NativePuncturedCover.isLocalHomeomorphOn_noncritical π y.val y.property)

def localMap (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    OpenPartialHomeomorph Y X := (oldLocalMap π y).transHomeomorph ψ

theorem localMap_center (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    y.val ∈ (localMap π ψ y).source :=
  (Classical.choose_spec (NativePuncturedCover.isLocalHomeomorphOn_noncritical π y.val y.property)).1

theorem localMap_function (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    (localMap π ψ y : Y → X) = projection π ψ := by
  funext z
  have h := (Classical.choose_spec (NativePuncturedCover.isLocalHomeomorphOn_noncritical π y.val y.property)).2
  change ψ (oldLocalMap π y z) = ψ (π.map z)
  exact congrArg ψ (congrFun h z).symm

theorem localMap_source (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    (localMap π ψ y).source = (oldLocalMap π y).source := rfl

theorem localMap_symm_apply (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) (x : X) :
    (localMap π ψ y).symm x = (oldLocalMap π y).symm (ψ.symm x) := rfl

theorem localMap_apply (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) (z : Y) :
    localMap π ψ y z = projection π ψ z := congrFun (localMap_function π ψ y) z

theorem localMap_source_noncritical (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π)
    {z : Y} (hz : z ∈ (localMap π ψ y).source) : z ∉ criticalSet π := by
  intro hc
  have htop : z ∈ Jacobians.Discharge.Manifold.criticalSetGeneral (projection π ψ) := by
    rw [NativeMovingCoverMap.topologicalCriticalSet_eq]
    exact hc
  apply htop
  refine ⟨(localMap π ψ y).source, (localMap π ψ y).open_source.mem_nhds hz, ?_⟩
  rw [← localMap_function π ψ y]
  exact (localMap π ψ y).injOn

def baseChart (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    OpenPartialHomeomorph X ℂ := chartAt ℂ (projection π ψ y.val)

def regularChart (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    OpenPartialHomeomorph Y ℂ := (localMap π ψ y).trans (baseChart π ψ y)

theorem regularChart_center (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) :
    y.val ∈ (regularChart π ψ y).source := by
  refine ⟨localMap_center π ψ y, ?_⟩
  change localMap π ψ y y.val ∈ (baseChart π ψ y).source
  rw [localMap_apply]
  exact mem_chart_source ℂ _

theorem regularChart_apply (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π) (z : Y) :
    regularChart π ψ y z = baseChart π ψ y (projection π ψ z) := by
  change baseChart π ψ y (localMap π ψ y z) = _
  rw [localMap_apply]

theorem regularChart_inverse_projection (π : Cover ωX ωY) (ψ : X ≃ₜ X) (y : RegularPoint π)
    {z : ℂ} (hz : z ∈ (regularChart π ψ y).target) :
    projection π ψ ((regularChart π ψ y).symm z) = (baseChart π ψ y).symm z := by
  change projection π ψ ((localMap π ψ y).symm ((baseChart π ψ y).symm z)) = _
  rw [← localMap_apply π ψ y]
  exact (localMap π ψ y).right_inv hz.2

variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

include hψ hInv

theorem exists_critical_neighborhood (y : CriticalPoint π) :
    ∃ U : Set Y, IsOpen U ∧ y.val ∈ U ∧ ∀ z ∈ U,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z ∧
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z = 0 ↔ z ∈ criticalSet π) := by
  have h := NativeMovingCoverRegularity.analytic_near_critical π ψ hψ hInv y.property
  obtain ⟨U, hUsub, hU, hy⟩ := mem_nhds_iff.mp h
  exact ⟨U, hU, hy, hUsub⟩

def criticalNeighborhood (y : CriticalPoint π) : Set Y :=
  Classical.choose (exists_critical_neighborhood π ψ hψ hInv y)

theorem criticalNeighborhood_open (y : CriticalPoint π) :
    IsOpen (criticalNeighborhood π ψ hψ hInv y) :=
  (Classical.choose_spec (exists_critical_neighborhood π ψ hψ hInv y)).1

theorem criticalNeighborhood_center (y : CriticalPoint π) :
    y.val ∈ criticalNeighborhood π ψ hψ hInv y :=
  (Classical.choose_spec (exists_critical_neighborhood π ψ hψ hInv y)).2.1

theorem criticalNeighborhood_analytic (y : CriticalPoint π) {z : Y}
    (hz : z ∈ criticalNeighborhood π ψ hψ hInv y) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z ∧
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (projection π ψ) z = 0 ↔ z ∈ criticalSet π) :=
  (Classical.choose_spec (exists_critical_neighborhood π ψ hψ hInv y)).2.2 z hz

def criticalChart (y : CriticalPoint π) : OpenPartialHomeomorph Y ℂ :=
  (chartAt ℂ y.val).restr (criticalNeighborhood π ψ hψ hInv y)

theorem criticalChart_center (y : CriticalPoint π) :
    y.val ∈ (criticalChart π ψ hψ hInv y).source := by
  refine ⟨mem_chart_source ℂ _, ?_⟩
  rw [(criticalNeighborhood_open π ψ hψ hInv y).interior_eq]
  exact criticalNeighborhood_center π ψ hψ hInv y

theorem criticalChart_mdifferentiable (y : CriticalPoint π) :
    (criticalChart π ψ hψ hInv y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  ComplexAtlasTools.mdifferentiable_restr _ (mdifferentiable_chart y.val) _

theorem regularChart_old_differentiable (i : RegularPoint π) (j : CriticalPoint π)
    {x : Y} (hx : x ∈ (regularChart π ψ i).source)
    (hxN : x ∈ criticalNeighborhood π ψ hψ hInv j) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (regularChart π ψ i) x ∧
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (regularChart π ψ i).symm (regularChart π ψ i x) := by
  let N := criticalNeighborhood π ψ hψ hInv j
  let f := (localMap π ψ i).restr N
  have hf : f.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    apply NativeMovingCoverRegularity.local_chart_holomorphic π ψ f
    · exact fun z _ => localMap_apply π ψ i z
    · intro z hz
      exact (criticalNeighborhood_analytic π ψ hψ hInv j (interior_subset hz.2)).1
    · intro z hz hzero
      have ha := criticalNeighborhood_analytic π ψ hψ hInv j (interior_subset hz.2)
      exact localMap_source_noncritical π ψ i hz.1 (ha.2.mp hzero)
  have hxF : x ∈ f.source := ⟨hx.1, by
    rw [(criticalNeighborhood_open π ψ hψ hInv j).interior_eq]
    exact hxN⟩
  let g := f.trans (baseChart π ψ i)
  have hg : g.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := hf.trans (mdifferentiable_chart (projection π ψ i.val))
  have hxG : x ∈ g.source := ⟨hxF, hx.2⟩
  exact ⟨hg.mdifferentiableAt hxG, hg.mdifferentiableAt_symm (g.map_source hxG)⟩

end VeechDichotomy.RelocatedCoverCharts
