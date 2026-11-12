module

public import VeechDichotomy.NativeLatticeMeasureSupport
public import VeechDichotomy.NativeTeichmullerRay
public import VeechDichotomy.CompactRecurrence
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! Almost-everywhere compact recurrence for the ACTUAL diagonal flow
on the native lattice quotient. It follows from its proved invariant
probability and topological Poincare recurrence. Every nonempty open set
contains a recurrent phase point. This is NOT the still outstanding
pointwise Veech return theorem for a specified minimal direction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeRecurrence

open LinearGroup NativeVeech NativeLatticeQuotient NativeLatticeMeasureSupport Set Filter Topology MeasureTheory

set_option backward.isDefEq.respectTransparency false

theorem diagonal_zero : NativeTeichmullerRay.diagonal 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [NativeTeichmullerRay.diagonal, Matrix.SpecialLinearGroup.coe_one]

def diagonalStep (Γ : Subgroup SL2) (x : SL2 ⧸ Γ) : SL2 ⧸ Γ := NativeTeichmullerRay.diagonal 1 • x

theorem iterate_step (Γ : Subgroup SL2) (n : ℕ) (x : SL2 ⧸ Γ) :
    ((diagonalStep Γ)^[n]) x = NativeTeichmullerRay.diagonal (n : ℝ) • x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, diagonal_zero, one_smul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change NativeTeichmullerRay.diagonal 1 • (NativeTeichmullerRay.diagonal (n : ℝ) • x) = _
    rw [smul_smul, ← NativeTeichmullerRay.diagonal_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, add_comm]

theorem ae_has_compact_returns (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    ∀ᵐ x ∂(invariantMeasure Γ hΓ), HasCompactReturns (fun t => NativeTeichmullerRay.diagonal t • x) := by
  let μ := invariantMeasure Γ hΓ
  have hpres : MeasurePreserving (diagonalStep Γ) μ μ := measurePreserving_smul (NativeTeichmullerRay.diagonal 1) μ
  have hrec := hpres.conservative.ae_frequently_mem_of_mem_nhds
  filter_upwards [hrec] with x hx
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have hfreq : ∃ᶠ n : ℕ in atTop, NativeTeichmullerRay.diagonal (n : ℝ) • x ∈ K := by
    simpa only [iterate_step] using hx K hKx
  refine ⟨K, hK, frequently_atTop.mpr ?_⟩
  intro R
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop R
  obtain ⟨n, hn, hge⟩ := (hfreq.and_eventually hlarge).exists
  exact ⟨(n : ℝ), hge, hn⟩

theorem exists_recurrent_in_open (Γ : Subgroup SL2) (hΓ : IsLattice Γ) {U : Set (SL2 ⧸ Γ)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, HasCompactReturns (fun t => NativeTeichmullerRay.diagonal t • x) := by
  let μ := invariantMeasure Γ hΓ
  have hpos : μ U ≠ 0 := ne_of_gt (open_measure_pos Γ μ hU hne)
  have hfreq : ∃ᵐ x ∂μ, x ∈ U := frequently_ae_mem_iff.mpr hpos
  exact (hfreq.and_eventually (ae_has_compact_returns Γ hΓ)).exists

end VeechDichotomy.NativeLatticeRecurrence
