module

public import VeechDichotomy.ConfigurationCoordinateChart

/-! The displacement parameters form a genuine open subset of a finite
dimensional complex vector space. Its inclusion is one global partial
chart, and it is homeomorphic to the previously constructed parameters. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexDisplacementParameters

open Set Topology LocalTranslationPlane

variable (m : ℕ)

abbrev Space := Fin m → ℂ

def domain : Set (Space m) := {a | ∀ i, ‖a i‖ < 1 / 2}

theorem domain_open : IsOpen (domain m) := by
  have heq : domain m = ⋂ i : Fin m, {a : Space m | ‖a i‖ < 1 / 2} := by ext a; simp [domain]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_lt ((continuous_apply i).norm) continuous_const

abbrev Parameters := domain m

def zero : Parameters m := ⟨0, fun _ => by norm_num⟩

def productHomeomorph : Parameters m ≃ₜ (Fin m → Parameter) where
  toFun a i := ⟨a.val i, a.property i⟩
  invFun a := ⟨fun i => (a i).val, fun i => (a i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

def chart : OpenPartialHomeomorph (Parameters m) (Space m) :=
  (⟨domain m, domain_open m⟩ : TopologicalSpace.Opens (Space m)).openPartialHomeomorphSubtypeCoe ⟨zero m⟩

@[simp] theorem chart_apply (a : Parameters m) : chart m a = a.val := rfl

@[simp] theorem chart_source : (chart m).source = univ := rfl

@[simp] theorem chart_target : (chart m).target = domain m :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target _ _

theorem inverse_value {a : Space m} (ha : a ∈ domain m) : ((chart m).symm a).val = a :=
  (chart m).right_inv (by rwa [chart_target])

variable {m} {X : Type*} [TopologicalSpace X]

def configurationHomeomorph (D : Fin m → PointTransportDisk.Disk (X := X)) :
    NativeConfigurationTransport.neighborhood D ≃ₜ Parameters m :=
  (ConfigurationCoordinateChart.homeomorph D).trans (productHomeomorph m).symm

theorem configuration_coordinate (D : Fin m → PointTransportDisk.Disk (X := X))
    (u : NativeConfigurationTransport.neighborhood D) (i : Fin m) :
    (configurationHomeomorph D u).val i = (D i).chart (u.val i) := rfl

end VeechDichotomy.ComplexDisplacementParameters
