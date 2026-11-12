module

public import VeechDichotomy.NativeLatticeQuotient
public import Mathlib.MeasureTheory.Measure.Support

/-! An actual invariant probability on the native homogeneous quotient
has positive measure on every nonempty open set. The proof uses support,
second countability and transitivity, not a supplied Haar/support field. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeMeasureSupport

open LinearGroup NativeVeech NativeLatticeQuotient Set Filter Topology MeasureTheory

variable (Γ : Subgroup SL2) (μ : Measure (SL2 ⧸ Γ))
  [IsProbabilityMeasure μ] [SMulInvariantMeasure SL2 (SL2 ⧸ Γ) μ]

theorem open_measure_pos {U : Set (SL2 ⧸ Γ)} (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  have hμ : μ ≠ 0 := by
    intro hzero
    have hz : μ univ = 0 := by rw [hzero]; rfl
    exact one_ne_zero ((measure_univ : μ univ = 1).symm.trans hz)
  obtain ⟨x₀, hx₀⟩ := Measure.nonempty_support hμ
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL2 x₀ x
  have hpre : (fun y : SL2 ⧸ Γ => g • y) ⁻¹' U ∈ 𝓝 x₀ :=
    (continuous_const_smul g).continuousAt (hU.mem_nhds (by rw [hg]; exact hx))
  have hp := (Measure.mem_support_iff_forall x₀).mp hx₀ _ hpre
  rwa [SMulInvariantMeasure.measure_preimage_smul g hU.measurableSet] at hp

instance openPosMeasure : μ.IsOpenPosMeasure where
  open_pos _U hU hne := ne_of_gt (open_measure_pos Γ μ hU hne)

theorem support_univ : μ.support = univ := Measure.support_eq_univ

end VeechDichotomy.NativeLatticeMeasureSupport
