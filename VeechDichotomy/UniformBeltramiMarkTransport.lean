module

public import VeechDichotomy.UniformBeltramiMarkData
public import VeechDichotomy.NativeBranchPointTransport
public import VeechDichotomy.PointTransportIsotopy

/-! One constructed family transports a finite marked tuple while the
native Beltrami fiber varies. Its inverse is jointly continuous as well.
The family is chosen once from the proved finite-composition theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiMarkTransport

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter}

structure Family (A : Data q b μ₀) where
  map : A.Parameters → X ≃ₜ X
  continuous_forward : Continuous (fun p : A.Parameters × X => map p.1 p.2)
  continuous_inverse : Continuous (fun p : A.Parameters × X => (map p.1).symm p.2)
  restriction : ∀ i p x, x ∈ A.support i → map p x = A.single i p x
  fixed : ∀ p x, (∀ i, x ∉ A.support i) → map p x = x

theorem nonempty_family (A : Data q b μ₀) : Nonempty (Family A) := by
  obtain ⟨F, hF, hInv, hown, hfixed⟩ := DisjointHomeomorphFamilies.exists_all
    A.support A.single A.support_disjoint A.continuous_single A.continuous_single_inverse
    (fun i p x hx => A.single_fixed i p hx)
  exact ⟨⟨F, hF, hInv, hown, hfixed⟩⟩

def chosenFamily (A : Data q b μ₀) : Family A := Classical.choice (nonempty_family A)

namespace Family

variable {A : Data q b μ₀} (F : Family A)

theorem identity (μ : A.Base) : F.map (μ, fun _ => DisjointPointTransport.zeroParameter) = Homeomorph.refl X := by
  ext x
  by_cases hx : ∃ i, x ∈ A.support i
  · obtain ⟨i, hi⟩ := hx
    rw [F.restriction i _ x hi]
    change UniformBeltramiTransport.oldTransport (A.disks i)
      (A.localBase μ i, DisjointPointTransport.zeroParameter) x = x
    rw [UniformBeltramiTransport.oldTransport_zero]
    rfl
  · exact F.fixed _ x (fun i hi => hx ⟨i, hi⟩)

def nativeMap (p : A.Parameters) :
    NativeBeltramiSurface.Surface q p.1.val ≃ₜ NativeBeltramiSurface.Surface q p.1.val :=
  ((NativeBeltramiSurface.toOriginal q p.1.val).trans (F.map p)).trans
    (NativeBeltramiSurface.toOriginal q p.1.val).symm

theorem nativeMap_point (p : A.Parameters) (x : NativeBeltramiSurface.Surface q p.1.val) :
    (F.nativeMap p x).point = F.map p x.point := rfl

def disks (_F : Family A) (μ : A.Base) (i : Fin m) : PointTransportDisk.Disk (X := NativeBeltramiSurface.Surface q μ.val) :=
  UniformBeltramiDisks.disk (A.disks i) (A.localBase μ i)

theorem native_restriction (p : A.Parameters) (i : Fin m)
    (x : NativeBeltramiSurface.Surface q p.1.val) (hx : x.point ∈ A.support i) :
    F.nativeMap p x = UniformBeltramiTransport.nativeTransport (A.disks i) (A.localParameter p i) x := by
  apply (NativeBeltramiSurface.toOriginal q p.1.val).injective
  exact F.restriction i p x.point hx

theorem disk_restriction (μ : A.Base) (i : Fin m) (δ : Fin m → LocalTranslationPlane.Parameter)
    (x : NativeBeltramiSurface.Surface q μ.val) (hx : x ∈ (F.disks μ i).support) :
    F.nativeMap (μ, δ) x = (F.disks μ i).transport (δ i) x := by
  have hOld : x.point ∈ A.support i := UniformBeltramiDisks.disk_support
    (A.disks i) (A.localBase μ i) ⟨x, hx, rfl⟩
  rw [F.native_restriction (μ, δ) i x hOld, UniformBeltramiTransport.nativeTransport_eq_disk]
  rfl

theorem moves (p : A.Parameters) (i : Fin m) :
    F.nativeMap p ⟨b i⟩ = (F.disks p.1 i).chart.symm (p.2 i).val := by
  rw [F.native_restriction p i ⟨b i⟩ (A.center_mem_support i),
    UniformBeltramiTransport.nativeTransport_eq_disk]
  exact (F.disks p.1 i).transport_center (p.2 i)

theorem distinct (p : A.Parameters) : Function.Injective (fun i => (F.disks p.1 i).chart.symm (p.2 i).val) := by
  intro i j hij
  apply A.injective
  have h := (F.nativeMap p).injective ((F.moves p i).trans (hij.trans (F.moves p j).symm))
  exact congrArg NativeBeltramiSurface.Surface.point h

theorem disk_holomorphic (μ : A.Base) (i : Fin m) : (F.disks μ i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  UniformBeltramiDisks.disk_holomorphic (A.disks i) (A.localBase μ i)

theorem holomorphic_near (p : A.Parameters) (i : Fin m) :
    ∀ᶠ x in 𝓝 (⟨b i⟩ : NativeBeltramiSurface.Surface q p.1.val),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F.nativeMap p) x :=
  NativeBranchPointTransport.holomorphic_near (F.disks p.1) (F.disk_holomorphic p.1)
    (fun δ => F.nativeMap (p.1, δ)) (fun j δ x hx => F.disk_restriction p.1 j δ x hx) p.2 i

theorem inverse_holomorphic_near (p : A.Parameters) (i : Fin m) :
    ∀ᶠ x in 𝓝 ((F.disks p.1 i).chart.symm (p.2 i).val),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F.nativeMap p).symm x :=
  NativeBranchPointTransport.inverse_holomorphic_near (F.disks p.1) (F.disk_holomorphic p.1)
    (fun δ => F.nativeMap (p.1, δ)) (fun j δ x hx => F.disk_restriction p.1 j δ x hx) p.2 i

theorem isotopy (μ : A.Base) (δ : Fin m → LocalTranslationPlane.Parameter) :
    ∃ J : unitInterval → X ≃ₜ X, J 0 = Homeomorph.refl X ∧ J 1 = F.map (μ, δ) ∧
      Continuous (fun p : unitInterval × X => J p.1 p.2) ∧
      Continuous (fun p : unitInterval × X => (J p.1).symm p.2) := by
  apply PointTransportIsotopy.exists_isotopy (fun δ => F.map (μ, δ))
  · exact F.continuous_forward.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  · exact F.continuous_inverse.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  · exact F.identity μ

end Family
end VeechDichotomy.UniformBeltramiMarkTransport
