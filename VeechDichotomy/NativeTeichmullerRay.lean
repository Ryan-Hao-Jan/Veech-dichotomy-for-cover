module

public import VeechDichotomy.NativeDeformationErgodicity
public import VeechDichotomy.NativeDeformationArea
public import VeechDichotomy.NativeDirectionRescaling
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual diagonal-deformation ray for any nonzero tested velocity.
A computed rotation sends the velocity to the positive vertical axis;
the diagonal matrix contracts it by exp(-t). Minimality, unique ergodicity
and total area are compared on the actual constructed compact curves.
Continuity of this family in a moduli topology is NOT asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeTeichmullerRay

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential
open LinearGroup LinearEquivalences NativeDeformationRegular WholeDeformedAtlas
open scoped Manifold ContDiff

def vertical : Plane := (0, 1)

def radius (v : Plane) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

theorem radius_pos {v : Plane} (hv : v ≠ 0) : 0 < radius v := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have hle : v.1 ^ 2 + v.2 ^ 2 ≤ 0 := le_of_not_gt h
  have h1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
  have h2 : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
  exact hv (Prod.ext h1 h2)

theorem radius_sq (v : Plane) : radius v ^ 2 = v.1 ^ 2 + v.2 ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

def rotationToVertical (v : Plane) (hv : v ≠ 0) : SL2 :=
  ⟨!![v.2 / radius v, -v.1 / radius v; v.1 / radius v, v.2 / radius v], by
    have hr : radius v ≠ 0 := (radius_pos hv).ne'
    rw [Matrix.det_fin_two]
    change (v.2 / radius v) * (v.2 / radius v) -
      (-v.1 / radius v) * (v.1 / radius v) = 1
    field_simp [hr]
    nlinarith [radius_sq v]⟩

theorem rotation_velocity (v : Plane) (hv : v ≠ 0) :
    planeEquiv (rotationToVertical v hv) v = (0, radius v) := by
  apply Prod.ext
  · change (v.2 / radius v) * v.1 + (-v.1 / radius v) * v.2 = 0
    ring
  · change (v.1 / radius v) * v.1 + (v.2 / radius v) * v.2 = radius v
    field_simp [(radius_pos hv).ne']
    nlinarith [radius_sq v]

def diagonal (t : ℝ) : SL2 :=
  ⟨!![Real.exp t, 0; 0, Real.exp (-t)], by simp [Matrix.det_fin_two, Real.exp_neg]⟩

theorem diagonal_add (s t : ℝ) : diagonal (s + t) = diagonal s * diagonal t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Real.exp_add, mul_comm]

theorem continuous_diagonal : Continuous diagonal := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> fun_prop

theorem diagonal_velocity (t : ℝ) (v : Plane) :
    planeEquiv (diagonal t) v = (Real.exp t * v.1, Real.exp (-t) * v.2) := by
  apply Prod.ext <;> simp [planeEquiv_apply, act, diagonal]

def matrix (v : Plane) (hv : v ≠ 0) (t : ℝ) : SL2 := diagonal t * rotationToVertical v hv

theorem continuous_matrix_ray (v : Plane) (hv : v ≠ 0) : Continuous (matrix v hv) :=
  continuous_diagonal.mul continuous_const

def contraction (v : Plane) (t : ℝ) : ℝ := Real.exp (-t) * radius v

theorem contraction_pos (v : Plane) (hv : v ≠ 0) (t : ℝ) : 0 < contraction v t :=
  mul_pos (Real.exp_pos _) (radius_pos hv)

theorem contraction_tendsto_zero (v : Plane) :
    Filter.Tendsto (contraction v) Filter.atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  simpa only [contraction, Function.comp_def, zero_mul] using! h.mul_const (radius v)

theorem contracted_velocity (v : Plane) (hv : v ≠ 0) (t : ℝ) :
    planeEquiv (matrix v hv t) v = contraction v t • vertical := by
  unfold matrix
  rw [planeEquiv_mul]
  change planeEquiv (diagonal t) (planeEquiv (rotationToVertical v hv) v) = _
  rw [rotation_velocity, diagonal_velocity]
  apply Prod.ext <;> simp [contraction, vertical]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0) (t : ℝ)

local instance : ChartedSpace ℂ (WholeSurface q (matrix v hv t)) :=
  WholeDeformedAtlas.chartedSpace q (matrix v hv t)
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q (matrix v hv t)) :=
  WholeDeformedAtlas.isComplexManifold q (matrix v hv t) ω

abbrev rayForm := transformed q (matrix v hv t)

theorem minimal_vertical_iff : NativeDynamics.MinimalDirection q v ↔
    NativeDynamics.MinimalDirection (rayForm q v hv t) vertical := by
  have h := NativeDeformationFlow.minimalDirection_iff q (matrix v hv t) v
  rw [contracted_velocity] at h
  exact h.trans (NativeDirectionRescaling.minimalDirection_iff (rayForm q v hv t)
    (contraction v t) (contraction_pos v hv t).ne' vertical)

theorem uniquelyErgodic_vertical_iff : NativeDynamics.UniquelyErgodicDirection q v ↔
    NativeDynamics.UniquelyErgodicDirection (rayForm q v hv t) vertical := by
  have h := NativeDeformationErgodicity.uniquelyErgodicDirection_iff q (matrix v hv t) v
  rw [contracted_velocity] at h
  exact h.trans (NativeDirectionRescaling.uniquelyErgodicDirection_iff (rayForm q v hv t)
    (contraction v t) (contraction_pos v hv t).ne' vertical)

theorem totalArea_constant : MNEC.NativeFiniteRegularArea.totalArea (rayForm q v hv t) =
    MNEC.NativeFiniteRegularArea.totalArea q := NativeDeformationArea.totalArea_eq q (matrix v hv t)

end VeechDichotomy.NativeTeichmullerRay
