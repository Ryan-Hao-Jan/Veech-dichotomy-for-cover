module

public import VeechDichotomy.UniformBeltramiMarkData
public import VeechDichotomy.ComplexDisplacementManifold

/-! A genuine open complex parameter domain for the common Beltrami
parameter and all marked-point displacements, with its inclusion chart.
It is homeomorphic to the parameters of the constructed transport family. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexBeltramiMarkParameters

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

abbrev Space := ℂ × (Fin m → ℂ)

def domain : Set (Space (m := m)) := {p | ‖p.1‖ < 1 ∧
  (∀ i, dist p.1 μ₀.val < (A.disks i).epsilon) ∧ ∀ i, ‖p.2 i‖ < 1 / 2}

theorem domain_open : IsOpen (domain A) := by
  have hnear : IsOpen {p : Space (m := m) | ∀ i, dist p.1 μ₀.val < (A.disks i).epsilon} := by
    have heq : {p : Space (m := m) | ∀ i, dist p.1 μ₀.val < (A.disks i).epsilon} =
        ⋂ i : Fin m, {p : Space (m := m) | dist p.1 μ₀.val < (A.disks i).epsilon} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt
      (continuous_fst.dist continuous_const) continuous_const
  exact (isOpen_lt continuous_fst.norm continuous_const).inter
    (hnear.inter ((ComplexDisplacementParameters.domain_open m).preimage continuous_snd))

abbrev Parameters := domain A

def reference : Parameters A := ⟨(μ₀.val, 0), μ₀.property,
  fun i => by simpa only [dist_self] using (A.disks i).epsilon_pos, fun _ => by norm_num⟩

def productHomeomorph : Parameters A ≃ₜ A.Parameters where
  toFun a := (⟨⟨a.val.1, a.property.1⟩, a.property.2.1⟩,
    fun i => ⟨a.val.2 i, a.property.2.2 i⟩)
  invFun p := ⟨(p.1.val.val, fun i => (p.2 i).val), p.1.val.property,
    p.1.property, fun i => (p.2 i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).subtype_mk _).prodMk
      (continuous_pi fun i => ((continuous_apply i).comp
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_pi fun i => continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).subtype_mk _

def chart : OpenPartialHomeomorph (Parameters A) (Space (m := m)) :=
  (⟨domain A, domain_open A⟩ : TopologicalSpace.Opens (Space (m := m))).openPartialHomeomorphSubtypeCoe ⟨reference A⟩

@[simp] theorem chart_apply (a : Parameters A) : chart A a = a.val := rfl
@[simp] theorem chart_source : (chart A).source = univ := rfl
@[simp] theorem chart_target : (chart A).target = domain A :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target _ _

theorem inverse_value {a : Space (m := m)} (ha : a ∈ domain A) : ((chart A).symm a).val = a :=
  (chart A).right_inv (by rwa [chart_target])

instance chartedSpace : ChartedSpace (Space (m := m)) (Parameters A) :=
  (chart A).singletonChartedSpace (chart_source A)

instance isComplexManifold (n : ℕ∞ω) : IsManifold 𝓘(ℂ, Space (m := m)) n (Parameters A) :=
  (chart A).isManifold_singleton (chart_source A)

theorem inclusion_holomorphic : ContMDiff 𝓘(ℂ, Space (m := m)) 𝓘(ℂ, Space (m := m)) ω
    (fun a : Parameters A => a.val) := by
  intro a
  exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) (mem_univ a)

end VeechDichotomy.ComplexBeltramiMarkParameters
