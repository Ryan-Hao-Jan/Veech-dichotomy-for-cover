module

public import VeechDichotomy.NativePointTransportDisk
public import VeechDichotomy.DisjointPointTransport
public import Mathlib.Tactic.Choose

/-! Disjoint holomorphic transport disks at an actual distinct native
branch tuple, and holomorphic germs for their combined whole-surface
homeomorphisms. No condition excludes zeros of the base one-form. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBranchPointTransport

open MNEC.NativeAbelianDifferential Set Filter Metric Topology PointTransportDisk
open LocalTranslationPlane DisjointPointTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

section Construction
variable [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem exists_disjoint_disks (q : Differential X) {m : ℕ} (b : Fin m → X)
    (hb : Function.Injective b) :
    ∃ D : Fin m → Disk (X := X),
      (∀ i, (D i).center = b i ∧ (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) ∧
      Pairwise (fun i j => Disjoint (D i).support (D j).support) := by
  classical
  obtain ⟨U, hU, hsep⟩ := (finite_range b).t2_separation
  choose D hcenter hsub hHol using (fun i : Fin m =>
    NativePointTransportDisk.exists_disk q (b i) (hU (b i)).2 (hU (b i)).1)
  refine ⟨D, fun i => ⟨hcenter i, hHol i⟩, ?_⟩
  intro i j hij
  exact (hsep (mem_range_self i) (mem_range_self j) (fun h => hij (hb h))).mono (hsub i) (hsub j)

end Construction

theorem holomorphic_near {ι : Type*} (D : ι → Disk (X := X))
    (hD : ∀ i, (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (δ : ι → Parameter) (i : ι) :
    ∀ᶠ x in 𝓝 (D i).center, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F δ) x := by
  have hsup := support_mem_nhds (D i) (D i).center_source (by rw [(D i).chart_center]; norm_num)
  obtain ⟨U, hUsub, hU, hcenter⟩ := mem_nhds_iff.mp hsup
  have hnear := NativePointTransportDisk.transport_holomorphic_near (D i) (hD i) (δ i)
  filter_upwards [hU.mem_nhds hcenter, hnear] with x hx hdiff
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with z hz
  exact hown i δ z (hUsub hz)

theorem inverse_holomorphic_near {ι : Type*} (D : ι → Disk (X := X))
    (hD : ∀ i, (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (δ : ι → Parameter) (i : ι) :
    ∀ᶠ x in 𝓝 ((D i).chart.symm (δ i).val), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F δ).symm x := by
  have hb : (D i).chart.symm (δ i).val ∈ (D i).chart.source :=
    (D i).chart.map_target ((D i).parameter_target (δ i))
  have hn : ‖(D i).chart ((D i).chart.symm (δ i).val)‖ < 2 := by
    rw [(D i).chart.right_inv ((D i).parameter_target (δ i))]
    have h := (δ i).property
    linarith
  have hsup := support_mem_nhds (D i) hb hn
  obtain ⟨U, hUsub, hU, hcenter⟩ := mem_nhds_iff.mp hsup
  have hnear := NativePointTransportDisk.transport_inverse_holomorphic_near (D i) (hD i) (δ i)
  filter_upwards [hU.mem_nhds hcenter, hnear] with x hx hdiff
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with z hz
  exact inverse_restriction D F hown δ i (hUsub hz)

omit [ChartedSpace ℂ X] in
theorem identity_at_zero {ι : Type*} (D : ι → Disk (X := X))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (hfixed : ∀ δ x, (∀ i, x ∉ (D i).support) → F δ x = x) :
    F (fun _ => zeroParameter) = Homeomorph.refl X := by
  ext x
  by_cases hx : ∃ i, x ∈ (D i).support
  · obtain ⟨i, hi⟩ := hx
    rw [hown i (fun _ => zeroParameter) x hi]
    exact transport_zero (D i) x
  · exact hfixed _ x (fun i hi => hx ⟨i, hi⟩)

end VeechDichotomy.NativeBranchPointTransport
