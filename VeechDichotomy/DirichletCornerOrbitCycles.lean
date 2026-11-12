module

public import VeechDichotomy.NativeCycleDeficit

/-! Actual orbit classes meeting the true Dirichlet corners, with
actual finite point cycles and actual cycle deficit masses. Different
classes have disjoint genuine cycles. Each selected class contains a
true corner, so its actual mass has the proved uniform lower bound. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerOrbitCycles

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicRegularCenters
open HyperbolicDirichletPointCycles DirichletCornerAngles
open scoped UpperHalfPlane

local instance : DecidableEq ℍ := Classical.decEq _

abbrev OrbitClass (Γ : Subgroup SL2) := Quotient (MulAction.orbitRel Γ ℍ)
def classOf (Γ : Subgroup SL2) (z : ℍ) : OrbitClass Γ := Quotient.mk (MulAction.orbitRel Γ ℍ) z
def cornerClasses (Γ : Subgroup SL2) (p : ℍ) : Set (OrbitClass Γ) := classOf Γ '' corners Γ p

def selected (Γ : Subgroup SL2) (p : ℍ) (q : cornerClasses Γ p) : ℍ := Classical.choose q.property

theorem selected_corner (Γ : Subgroup SL2) (p : ℍ) (q : cornerClasses Γ p) : selected Γ p q ∈ corners Γ p :=
  (Classical.choose_spec q.property).1

theorem selected_class (Γ : Subgroup SL2) (p : ℍ) (q : cornerClasses Γ p) : classOf Γ (selected Γ p q) = q.val :=
  (Classical.choose_spec q.property).2

theorem class_eq_of_orbit (Γ : Subgroup SL2) (z w : ℍ) (hz : z ∈ MulAction.orbit Γ w) : classOf Γ z = classOf Γ w :=
  Quotient.sound hz

theorem orbit_of_class_eq (Γ : Subgroup SL2) (z w : ℍ) (hz : classOf Γ z = classOf Γ w) : z ∈ MulAction.orbit Γ w :=
  Quotient.exact hz

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

def cycleFinset (p : ℍ) (q : cornerClasses Γ p) : Finset ℍ := (cycle_finite Γ p (selected Γ p q)).toFinset

theorem coe_cycleFinset (p : ℍ) (q : cornerClasses Γ p) :
    (cycleFinset Γ p q : Set ℍ) = region Γ p ∩ MulAction.orbit Γ (selected Γ p q) :=
  (cycle_finite Γ p (selected Γ p q)).coe_toFinset

theorem cycle_mem_region (p : ℍ) (q : cornerClasses Γ p) {w : ℍ} (hw : w ∈ cycleFinset Γ p q) : w ∈ region Γ p := by
  have hm : w ∈ (cycleFinset Γ p q : Set ℍ) := hw
  rw [coe_cycleFinset] at hm
  exact hm.1

theorem cycles_disjoint (p : ℍ) {q r : cornerClasses Γ p} (hqr : q ≠ r) :
    Disjoint (cycleFinset Γ p q) (cycleFinset Γ p r) := by
  apply Finset.disjoint_left.mpr
  intro w hwq hwr
  have hq : w ∈ (cycleFinset Γ p q : Set ℍ) := hwq
  have hr : w ∈ (cycleFinset Γ p r : Set ℍ) := hwr
  rw [coe_cycleFinset] at hq hr
  have hqw : classOf Γ w = q.val := (class_eq_of_orbit Γ w (selected Γ p q) hq.2).trans (selected_class Γ p q)
  have hrw : classOf Γ w = r.val := (class_eq_of_orbit Γ w (selected Γ p r) hr.2).trans (selected_class Γ p r)
  exact hqr (Subtype.ext (hqw.symm.trans hrw))

def mass (p : ℍ) (q : cornerClasses Γ p) : ℝ := ∑ w ∈ cycleFinset Γ p q, deficit Γ p w

theorem mass_eq_sum (p : ℍ) (q : cornerClasses Γ p) :
    mass Γ p q = ∑ w : EffectiveCycleSums.cycle Γ p (selected Γ p q), deficit Γ p w.val := by
  apply Finset.sum_subtype (cycleFinset Γ p q) _ (deficit Γ p)
  intro w
  change w ∈ (cycleFinset Γ p q : Set ℍ) ↔ w ∈ region Γ p ∩ MulAction.orbit Γ (selected Γ p q)
  rw [coe_cycleFinset]

theorem mass_ge_pi_div_three (p : ℍ) (hp : RegularCenter Γ p) (q : cornerClasses Γ p) : Real.pi / 3 ≤ mass Γ p q := by
  rw [mass_eq_sum]
  exact NativeCycleDeficit.cycle_deficit_ge_pi_div_three Γ p hp (selected Γ p q) (selected_corner Γ p q)

end VeechDichotomy.DirichletCornerOrbitCycles
