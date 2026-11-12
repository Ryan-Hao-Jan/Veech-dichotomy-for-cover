module

public import VeechDichotomy.NativeConfigurationTransport

/-! The explicit coordinate homeomorphism from the actual marked-tuple
neighborhood to the product of small complex displacement disks. This
identifies its parameter topology independently of the transport family.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ConfigurationCoordinateChart

open Set Topology PointTransportDisk NativeConfigurationTransport LocalTranslationPlane

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] {m : ℕ}

def target (D : Fin m → Disk (X := X)) (δ : Fin m → Parameter) : neighborhood D :=
  ⟨fun i => (D i).chart.symm (δ i).val, fun i =>
    ⟨(D i).chart.map_target ((D i).parameter_target (δ i)), by
      rw [(D i).chart.right_inv ((D i).parameter_target (δ i))]
      exact (δ i).property⟩⟩

theorem continuous_target (D : Fin m → Disk (X := X)) : Continuous (target D) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (D i).chart.symm.continuousOn.comp_continuous
    (continuous_subtype_val.comp (continuous_apply i)) (fun δ => (D i).parameter_target (δ i))

def homeomorph (D : Fin m → Disk (X := X)) : neighborhood D ≃ₜ (Fin m → Parameter) where
  toFun := parameters D
  invFun := target D
  left_inv u := by
    apply Subtype.ext
    funext i
    exact (D i).chart.left_inv (u.property i).1
  right_inv δ := by
    funext i
    apply Subtype.ext
    exact (D i).chart.right_inv ((D i).parameter_target (δ i))
  continuous_toFun := parameters_continuous D
  continuous_invFun := continuous_target D

end VeechDichotomy.ConfigurationCoordinateChart
