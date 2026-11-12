module

public import VeechDichotomy.DisjointPointTransportUniform
public import VeechDichotomy.NativeLocalCoverFamily

/-! Constructed marked transports with parameter-independent open regions
of biholomorphicity. The additional analytic data is proved from the actual
disjoint chart transports, including when a mark is a differential zero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeUniformMarkTransport

open MNEC.NativeAbelianDifferential Set Filter Metric Topology PointTransportDisk
open LocalTranslationPlane DisjointPointTransport NativeConfigurationTransport
open NativeLocalCoverFamily PointTransportUniform
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {m : ℕ}

structure Transport (b : Fin m → X) where
  marks : MarkTransport b
  region : Fin m → Set X
  region_open : ∀ i, IsOpen (region i)
  region_contains : ∀ i, b i ∈ region i
  holomorphic : ∀ u : marks.neighborhood, ∀ i, ∀ x ∈ region i,
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (marks.transport u) x
  inverse_holomorphic : ∀ u : marks.neighborhood, ∀ i, ∀ x ∈ region i,
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (marks.transport u).symm (marks.transport u x)

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem nonempty_transport (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) :
    Nonempty (Transport b) := by
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
  have hid : ∀ u : Ω, u.val = b → Ψ u = Homeomorph.refl X := by
    intro u hu
    have hp : parameters D u = fun _ => zeroParameter := by
      funext i
      apply Subtype.ext
      change (D i).chart (u.val i) = 0
      rw [hu, ← (hD i).1, (D i).chart_center]
    change F (parameters D u) = Homeomorph.refl X
    rw [hp]
    exact NativeBranchPointTransport.identity_at_zero D F hown hfixed
  let T : MarkTransport b :=
    { neighborhood := Ω
      open_neighborhood := neighborhood_open D
      contains := hbΩ
      distinct := hconf
      transport := Ψ
      continuous_transport := hΨ
      continuous_inverse := hΨInv
      identity := hid
      moves := hmoves
      holomorphic_near := by
        intro u i
        have h := NativeBranchPointTransport.holomorphic_near D (fun i => (hD i).2) F hown (parameters D u) i
        simpa only [(hD i).1] using h
      inverse_holomorphic_near := by
        intro u i
        have h := NativeBranchPointTransport.inverse_holomorphic_near D (fun i => (hD i).2) F hown (parameters D u) i
        have heq : (D i).chart.symm ((parameters D u i).val) = u.val i := (D i).chart.left_inv (u.property i).1
        rw [heq] at h
        exact h
      isotopy := fun u => PointTransportIsotopy.exists_isotopy F hF hInv
        (NativeBranchPointTransport.identity_at_zero D F hown hfixed) (parameters D u) }
  refine ⟨{ marks := T
            region := fun i => innerDisk (D i)
            region_open := fun i => innerDisk_open (D i)
            region_contains := ?_
            holomorphic := ?_
            inverse_holomorphic := ?_ }⟩
  · intro i
    rw [← (hD i).1]
    exact center_mem_innerDisk (D i)
  · intro u i x hx
    exact DisjointPointTransportUniform.holomorphic_at D (fun i => (hD i).2) F hown (parameters D u) i hx
  · intro u i x hx
    exact DisjointPointTransportUniform.inverse_holomorphic_at D (fun i => (hD i).2) F hown (parameters D u) i hx

def chosenTransport (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) : Transport b :=
  Classical.choice (nonempty_transport q b hb)

end VeechDichotomy.NativeUniformMarkTransport
