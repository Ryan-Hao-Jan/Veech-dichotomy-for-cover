module

public import VeechDichotomy.UniformBeltramiMarkSections

/-! Exact forward and inverse translation formulas for the constructed
whole-surface family, in the actual varying normalized fiber charts.
Ambient complex parameters are included explicitly for later germ calculus. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiTransportFormulas

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} {A : Data q b μ₀} (F : Family A)

theorem native_forward (p : A.Parameters) (i : Fin m) {z : ℂ} (hz : ‖z‖ < 1) :
    F.nativeMap p ((F.disks p.1 i).chart.symm z) = (F.disks p.1 i).chart.symm (z + (p.2 i).val) := by
  have hzC : z ∈ closedBall (0 : ℂ) 2 := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hzT := (F.disks p.1 i).closedBall_target hzC
  rw [F.disk_restriction p.1 i p.2 _ ⟨z, hzC, rfl⟩,
    PointTransportDisk.Disk.transport_apply_of_source _ _ ((F.disks p.1 i).chart.map_target hzT),
    (F.disks p.1 i).chart.right_inv hzT, LocalTranslationPlane.homeomorph_apply,
    LocalTranslationPlane.move_translation hz.le]

theorem native_inverse (p : A.Parameters) (i : Fin m) {w : ℂ} (hw : ‖w - (p.2 i).val‖ < 1) :
    (F.nativeMap p).symm ((F.disks p.1 i).chart.symm w) = (F.disks p.1 i).chart.symm (w - (p.2 i).val) := by
  apply (F.nativeMap p).injective
  rw [Homeomorph.apply_symm_apply, native_forward F p i hw, sub_add_cancel]

def ambientParameters (a : ComplexBeltramiMarkParameters.Space (m := m)) : A.Parameters :=
  ComplexBeltramiMarkParameters.productHomeomorph A ((ComplexBeltramiMarkParameters.chart A).symm a)

theorem parameter_values {a : ComplexBeltramiMarkParameters.Space (m := m)}
    (ha : a ∈ ComplexBeltramiMarkParameters.domain A) :
    (ambientParameters (A := A) a).1.val.val = a.1 ∧
      ∀ i, ((ambientParameters (A := A) a).2 i).val = a.2 i := by
  have h := ComplexBeltramiMarkParameters.inverse_value A ha
  exact ⟨congrArg Prod.fst h, fun i => congrArg (fun p => p.2 i) h⟩

def ambientForward (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :
    NativeBeltramiTotalSpace.TotalSpace q :=
  let a := ambientParameters (A := A) p.1
  ⟨(a.1.val, F.map a ((F.disks a.1 i).chart.symm p.2).point)⟩

def ambientInverse (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :
    NativeBeltramiTotalSpace.TotalSpace q :=
  let a := ambientParameters (A := A) p.1
  ⟨(a.1.val, (F.map a).symm ((F.disks a.1 i).chart.symm p.2).point)⟩

theorem forward_formula (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    (ha : p.1 ∈ ComplexBeltramiMarkParameters.domain A) (hz : ‖p.2‖ < 1) :
    ambientForward F i p = NormalizedBeltramiTotalInverse.inverse (A.disks i) (p.1.1, p.2 + p.1.2 i) := by
  let a := ambientParameters (A := A) p.1
  have hn := congrArg NativeBeltramiSurface.Surface.point (native_forward F a i hz)
  have hInv := NormalizedBeltramiTotalInverse.inverse_value (A.disks i) (A.localBase a.1 i) (p.2 + (a.2 i).val)
  change NormalizedBeltramiTotalInverse.inverse (A.disks i) (a.1.val.val, p.2 + (a.2 i).val) = _ at hInv
  have hvalue : ambientForward F i p = NormalizedBeltramiTotalInverse.inverse (A.disks i) (a.1.val.val, p.2 + (a.2 i).val) := by
    rw [hInv]
    apply (NativeBeltramiTotalSpace.toProduct q).injective
    exact Prod.ext rfl hn
  have hv := parameter_values ha
  exact hvalue.trans (congrArg (NormalizedBeltramiTotalInverse.inverse (A.disks i)) (Prod.ext hv.1 (congrArg (p.2 + ·) (hv.2 i))))

theorem inverse_formula (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    (ha : p.1 ∈ ComplexBeltramiMarkParameters.domain A) (hw : ‖p.2 - p.1.2 i‖ < 1) :
    ambientInverse F i p = NormalizedBeltramiTotalInverse.inverse (A.disks i) (p.1.1, p.2 - p.1.2 i) := by
  let a := ambientParameters (A := A) p.1
  have hv := parameter_values ha
  have hw' : ‖p.2 - (a.2 i).val‖ < 1 := by rw [hv.2 i]; exact hw
  have hn := congrArg NativeBeltramiSurface.Surface.point (native_inverse F a i hw')
  have hInv := NormalizedBeltramiTotalInverse.inverse_value (A.disks i) (A.localBase a.1 i) (p.2 - (a.2 i).val)
  change NormalizedBeltramiTotalInverse.inverse (A.disks i) (a.1.val.val, p.2 - (a.2 i).val) = _ at hInv
  have hvalue : ambientInverse F i p = NormalizedBeltramiTotalInverse.inverse (A.disks i) (a.1.val.val, p.2 - (a.2 i).val) := by
    rw [hInv]
    apply (NativeBeltramiTotalSpace.toProduct q).injective
    exact Prod.ext rfl hn
  exact hvalue.trans (congrArg (NormalizedBeltramiTotalInverse.inverse (A.disks i)) (Prod.ext hv.1 (congrArg (p.2 - ·) (hv.2 i))))

end VeechDichotomy.UniformBeltramiTransportFormulas
