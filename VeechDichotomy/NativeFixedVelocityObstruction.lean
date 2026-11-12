module

public import VeechDichotomy.NativeParabolicDirectionObstruction
public import VeechDichotomy.SL2FixedVelocityNormalForm

/-! On a native genus-at-least-two surface, an actual derivative fixing
the velocity of a dense complete orbit must be the identity. A derivative
reversing that velocity must have square equal to the identity. Thus the
parabolic obstruction accepts geometric cusp matrices without requiring
the caller to supply their shear normal form. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFixedVelocityObstruction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeVeech LinearGroup LinearEquivalences NativeTeichmullerRay
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (hgenus : 2 ≤ genus X) (v : Plane) (hv : v ≠ 0)
  (x : CompleteOrbits q v) (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val))

include hgenus hv x hdense

theorem derivative_eq_one {B : SL2} (hB : B ∈ derivativeGroup q) (hfix : planeEquiv B v = v) : B = 1 := by
  by_contra hne
  have hAv : planeEquiv (rotationToVertical v hv) v = radius v • vertical := by
    rw [rotation_velocity]
    ext <;> simp [vertical]
  obtain ⟨a, ha, hnormal⟩ := SL2FixedVelocityNormalForm.nontrivial_conjugate_normal_form
    (rotationToVertical v hv) B v (radius_pos hv).ne' hAv hfix hne
  rw [hnormal] at hB
  exact NativeParabolicDirectionObstruction.rotated_shear_not_mem q hgenus v hv x hdense ha hB

theorem square_eq_one_of_reverses {B : SL2} (hB : B ∈ derivativeGroup q)
    (hreverse : planeEquiv B v = -v) : B ^ 2 = 1 := by
  have hfix : planeEquiv (B ^ 2) v = v := by
    rw [pow_two, planeEquiv_mul]
    change planeEquiv B (planeEquiv B v) = v
    rw [hreverse, map_neg, hreverse, neg_neg]
  exact derivative_eq_one q hgenus v hv x hdense ((derivativeGroup q).pow_mem hB 2) hfix

theorem square_eq_one_of_preserves_sign {B : SL2} (hB : B ∈ derivativeGroup q)
    (hfix : planeEquiv B v = v ∨ planeEquiv B v = -v) : B ^ 2 = 1 := by
  rcases hfix with hf | hr
  · rw [derivative_eq_one q hgenus v hv x hdense hB hf, one_pow]
  · exact square_eq_one_of_reverses q hgenus v hv x hdense hB hr

end VeechDichotomy.NativeFixedVelocityObstruction
