module

public import VeechDichotomy.BeltramiPlaneTransport
public import VeechDichotomy.NativePointTransportDisk
public import VeechDichotomy.PointTransportUniform

/-! Actual whole-surface point transports varying jointly with the base
parameter and displacement. Compact support is fixed in the original
surface. In each native deformed fiber they are EXACTLY the constructed
normalized-disk transports, so the native holomorphic germs are derived. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiTransport

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiDiskData UniformBeltramiDisks
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : X} {μ₀ : Parameter} {U : Set X} (D : Data q b μ₀ U)

def support : Set X := (NativePowerCharts.chosen q b).chart.symm '' closedBall 0 D.oldRadius

theorem support_compact : IsCompact (support D) :=
  ChartHomeomorphExtension.support_compact (NativePowerCharts.chosen q b).chart (isCompact_closedBall _ _) D.old_target

theorem support_subset : support D ⊆ U := D.old_support

def oldTransport (p : BeltramiPlaneTransport.Parameters D) : X ≃ₜ X :=
  ChartHomeomorphExtension.homeomorph (NativePowerCharts.chosen q b).chart (isCompact_closedBall _ _) D.old_target
    (BeltramiPlaneTransport.transport D) (BeltramiPlaneTransport.preserves_target D)
    (BeltramiPlaneTransport.inverse_preserves_target D) (BeltramiPlaneTransport.fixed_outside D)
    (BeltramiPlaneTransport.continuous_transport D) (BeltramiPlaneTransport.continuous_inverse D) p

theorem continuous_oldTransport : Continuous (fun p : BeltramiPlaneTransport.Parameters D × X => oldTransport D p.1 p.2) :=
  ChartHomeomorphExtension.continuous_value (NativePowerCharts.chosen q b).chart (isCompact_closedBall _ _) D.old_target
    (BeltramiPlaneTransport.transport D) (BeltramiPlaneTransport.preserves_target D) (BeltramiPlaneTransport.fixed_outside D)
    (BeltramiPlaneTransport.continuous_transport D)

theorem continuous_oldInverse : Continuous (fun p : BeltramiPlaneTransport.Parameters D × X => (oldTransport D p.1).symm p.2) :=
  ChartHomeomorphExtension.continuous_value (NativePowerCharts.chosen q b).chart (isCompact_closedBall _ _) D.old_target
    (fun p => (BeltramiPlaneTransport.transport D p).symm) (BeltramiPlaneTransport.inverse_preserves_target D)
    (BeltramiPlaneTransport.inverse_fixed_outside D) (BeltramiPlaneTransport.continuous_inverse D)

theorem oldTransport_fixed (p : BeltramiPlaneTransport.Parameters D) {x : X} (hx : x ∉ support D) : oldTransport D p x = x :=
  ChartHomeomorphExtension.value_fixed (NativePowerCharts.chosen q b).chart (BeltramiPlaneTransport.transport D p)
    (BeltramiPlaneTransport.fixed_outside D p) hx

def nativeTransport (p : BeltramiPlaneTransport.Parameters D) :
    NativeBeltramiSurface.Surface q p.1.val ≃ₜ NativeBeltramiSurface.Surface q p.1.val :=
  ((NativeBeltramiSurface.toOriginal q p.1.val).trans (oldTransport D p)).trans (NativeBeltramiSurface.toOriginal q p.1.val).symm

theorem nativeTransport_point (p : BeltramiPlaneTransport.Parameters D) (x : NativeBeltramiSurface.Surface q p.1.val) :
    (nativeTransport D p x).point = oldTransport D p x.point := rfl

theorem nativeTransport_eq_disk (p : BeltramiPlaneTransport.Parameters D) :
    nativeTransport D p = (disk D p.1).transport p.2 := by
  ext x
  apply (NativeBeltramiSurface.toOriginal q p.1.val).injective
  change oldTransport D p x.point = ((disk D p.1).transport p.2 x).point
  by_cases hx : x.point ∈ (NativePowerCharts.chosen q b).chart.source
  · have hxD : x ∈ (disk D p.1).chart.source := hx
    rw [PointTransportDisk.Disk.transport_apply_of_source (disk D p.1) p.2 hxD]
    change ChartHomeomorphExtension.value (NativePowerCharts.chosen q b).chart (BeltramiPlaneTransport.transport D p) x.point = _
    rw [ChartHomeomorphExtension.value, ite_eq_left hx]
    rfl
  · have hxD : x ∉ (disk D p.1).chart.source := hx
    change ChartHomeomorphExtension.value (NativePowerCharts.chosen q b).chart (BeltramiPlaneTransport.transport D p) x.point =
      (ChartHomeomorphExtension.value (disk D p.1).chart (LocalTranslationPlane.homeomorph p.2) x).point
    rw [ChartHomeomorphExtension.value, ite_eq_right hx, ChartHomeomorphExtension.value, ite_eq_right hxD]

theorem oldTransport_zero (μ : Near D) : oldTransport D (μ, DisjointPointTransport.zeroParameter) = Homeomorph.refl X := by
  ext x
  have h := DisjointPointTransport.transport_zero (disk D μ) ((NativeBeltramiSurface.toOriginal q μ.val).symm x)
  rw [← nativeTransport_eq_disk D (μ, DisjointPointTransport.zeroParameter)] at h
  exact congrArg (NativeBeltramiSurface.toOriginal q μ.val) h

theorem holomorphic_near (p : BeltramiPlaneTransport.Parameters D) :
    ∀ᶠ x in 𝓝 (⟨b⟩ : NativeBeltramiSurface.Surface q p.1.val), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (nativeTransport D p) x := by
  rw [nativeTransport_eq_disk]
  exact NativePointTransportDisk.transport_holomorphic_near (disk D p.1) (disk_holomorphic D p.1) p.2

theorem inverse_holomorphic_near (p : BeltramiPlaneTransport.Parameters D) :
    ∀ᶠ x in 𝓝 ((disk D p.1).chart.symm p.2.val), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (nativeTransport D p).symm x := by
  rw [nativeTransport_eq_disk]
  exact NativePointTransportDisk.transport_inverse_holomorphic_near (disk D p.1) (disk_holomorphic D p.1) p.2

end VeechDichotomy.UniformBeltramiTransport
