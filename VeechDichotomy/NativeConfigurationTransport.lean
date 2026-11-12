module

public import VeechDichotomy.NativeBranchPointTransport
public import VeechDichotomy.Configuration
public import VeechDichotomy.PointTransportIsotopy

/-! A genuine local transport family for every ordered distinct tuple
on a native compact complex curve. It sends the reference tuple to each
nearby tuple, is jointly continuous in both directions, and is holomorphic
near all old/new marks. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeConfigurationTransport

open MNEC.NativeAbelianDifferential Set Filter Metric Topology PointTransportDisk
open LocalTranslationPlane DisjointPointTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] {m : ℕ}

def neighborhood (D : Fin m → Disk (X := X)) : Set (Fin m → X) :=
  {u | ∀ i, u i ∈ (D i).chart.source ∧ ‖(D i).chart (u i)‖ < 1 / 2}

theorem neighborhood_open (D : Fin m → Disk (X := X)) : IsOpen (neighborhood D) := by
  have heq : neighborhood D = ⋂ i : Fin m,
      (fun u : Fin m → X => u i) ⁻¹'
        ((D i).chart.source ∩ (D i).chart ⁻¹' ball (0 : ℂ) (1 / 2)) := by
    ext u
    simp only [neighborhood, mem_ofPred_eq, mem_iInter, mem_preimage, mem_inter_iff, mem_ball, dist_zero_right]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact ((D i).chart.continuousOn.isOpen_inter_preimage (D i).chart.open_source isOpen_ball).preimage
    (continuous_apply i)

def parameters (D : Fin m → Disk (X := X)) (u : neighborhood D) : Fin m → Parameter :=
  fun i => ⟨(D i).chart (u.val i), (u.property i).2⟩

theorem parameters_continuous (D : Fin m → Disk (X := X)) : Continuous (parameters D) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact (D i).chart.continuousOn.comp_continuous
    ((continuous_apply i).comp continuous_subtype_val) (fun u => (u.property i).1)

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem exists_local_transport (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) :
    ∃ Ω : Set (Fin m → X), IsOpen Ω ∧ b ∈ Ω ∧ Ω ⊆ configuration m X ∧
      ∃ Ψ : Ω → X ≃ₜ X,
        Continuous (fun p : Ω × X => Ψ p.1 p.2) ∧
        Continuous (fun p : Ω × X => (Ψ p.1).symm p.2) ∧
        (∀ u : Ω, u.val = b → Ψ u = Homeomorph.refl X) ∧
        (∀ u : Ω, ∀ i, Ψ u (b i) = u.val i) ∧
        (∀ u : Ω, ∀ i, ∀ᶠ x in 𝓝 (b i), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Ψ u) x) ∧
        (∀ u : Ω, ∀ i, ∀ᶠ x in 𝓝 (u.val i), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Ψ u).symm x) ∧
        (∀ u : Ω, ∃ J : unitInterval → X ≃ₜ X, J 0 = Homeomorph.refl X ∧ J 1 = Ψ u ∧
          Continuous (fun p : unitInterval × X => J p.1 p.2) ∧
          Continuous (fun p : unitInterval × X => (J p.1).symm p.2)) := by
  classical
  obtain ⟨D, hD, hdisj⟩ := NativeBranchPointTransport.exists_disjoint_disks q b hb
  obtain ⟨F, hF, hInv, hown, hfixed⟩ := exists_all D hdisj
  let Ω := neighborhood D
  have hbΩ : b ∈ Ω := by
    intro i
    have hc : b i ∈ (D i).chart.source := by rw [← (hD i).1]; exact (D i).center_source
    have hz : (D i).chart (b i) = 0 := by rw [← (hD i).1]; exact (D i).chart_center
    exact ⟨hc, by rw [hz]; norm_num⟩
  let Ψ : Ω → X ≃ₜ X := fun u => F (parameters D u)
  have hΨ : Continuous (fun p : Ω × X => Ψ p.1 p.2) :=
    hF.comp (((parameters_continuous D).comp continuous_fst).prodMk continuous_snd)
  have hΨInv : Continuous (fun p : Ω × X => (Ψ p.1).symm p.2) :=
    hInv.comp (((parameters_continuous D).comp continuous_fst).prodMk continuous_snd)
  have hmoves (u : Ω) (i : Fin m) : Ψ u (b i) = u.val i := by
    have h := hown i (parameters D u) (D i).center (center_mem_support (D i))
    rw [(D i).transport_center] at h
    have h' : Ψ u (b i) = (D i).chart.symm ((D i).chart (u.val i)) := by
      change F (parameters D u) (b i) = (D i).chart.symm ((parameters D u i).val)
      simpa only [(hD i).1] using h
    exact h'.trans ((D i).chart.left_inv (u.property i).1)
  have hconf : Ω ⊆ configuration m X := by
    intro u hu i j hij
    apply hb
    apply (Ψ ⟨u, hu⟩).injective
    rw [hmoves ⟨u, hu⟩ i, hmoves ⟨u, hu⟩ j]
    exact hij
  refine ⟨Ω, neighborhood_open D, hbΩ, hconf, Ψ, hΨ, hΨInv, ?_, hmoves, ?_, ?_, ?_⟩
  · intro u hu
    have hp : parameters D u = fun _ => zeroParameter := by
      funext i
      apply Subtype.ext
      change (D i).chart (u.val i) = 0
      rw [hu, ← (hD i).1, (D i).chart_center]
    change F (parameters D u) = Homeomorph.refl X
    rw [hp]
    exact NativeBranchPointTransport.identity_at_zero D F hown hfixed
  · intro u i
    have h := NativeBranchPointTransport.holomorphic_near D (fun i => (hD i).2) F hown (parameters D u) i
    simpa only [(hD i).1] using h
  · intro u i
    have h := NativeBranchPointTransport.inverse_holomorphic_near D (fun i => (hD i).2) F hown (parameters D u) i
    have heq : (D i).chart.symm ((parameters D u i).val) = u.val i := (D i).chart.left_inv (u.property i).1
    rw [heq] at h
    exact h
  · intro u
    exact PointTransportIsotopy.exists_isotopy F hF hInv
      (NativeBranchPointTransport.identity_at_zero D F hown hfixed) (parameters D u)

end VeechDichotomy.NativeConfigurationTransport
