module

public import VeechDichotomy.RadialIdealAngles

/-! Every finite ideal polygon in the actual closure of an actual
finite-area Dirichlet region consumes its full ideal angle deficit.
The bound is obtained from actual finite polygons inside that region
and their proved corner-angle limits, without an ideal-area axiom. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletIdealAreaBudget

open LinearGroup Set Filter Topology MeasureTheory HyperbolicDirichletRegions
open DirichletIdealRadialPoints IdealRadialLimits RadialPolygonOrder HyperbolicPolygonAngles
open scoped UpperHalfPlane ENNReal

theorem ordered_area_bound (Γ : Subgroup SL2) (p : ℍ) (hfinite : volume (region Γ p) ≠ ⊤)
    (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (ha : a ∈ idealBoundary Γ p) (hv : ∀ i, v i ∈ idealBoundary Γ p)
    (haI : a ≠ Complex.I) (hvI : ∀ i, v i ≠ Complex.I)
    (horder : PlanarPolygonAngles.StrictlyOrdered a v n) :
    (n : ℝ) * Real.pi ≤ (volume (region Γ p)).toReal := by
  have hangles := RadialIdealAngles.polygonAngleSum_tendsto_zero p a v n hn ha.2 (fun i => (hv i).2)
    haI hvI horder
  have hlim : Tendsto (fun k => (n : ℝ) * Real.pi -
      polygonAngleSum (approx p a ha.2 k) (fun i => approx p (v i) (hv i).2 k) n)
      atTop (𝓝 ((n : ℝ) * Real.pi)) := by
    simpa only [sub_zero] using! (tendsto_const_nhds (x := (n : ℝ) * Real.pi)).sub hangles
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  rw [← HyperbolicPolygonAreaAngle.real_area_formula _ _ n hn
    (approx_strict p a v n ha.2 (fun i => (hv i).2) horder k)]
  exact ENNReal.toReal_mono hfinite (measure_mono
    (NativeDirichletPolygonDeficit.polygon_subset_dirichlet Γ p _ _ n
      (approx_mem_region Γ p ha k) (fun i _ => approx_mem_region Γ p (hv i) k)))

theorem finite_family_bound (Γ : Subgroup SL2) (p : ℍ) (hfinite : volume (region Γ p) ≠ ⊤)
    (S : Finset ℂ) (hS : ∀ u ∈ S, u ∈ idealBoundary Γ p ∧ u ≠ Complex.I) (hcard : 3 ≤ S.card) :
    (S.card : ℝ) * Real.pi ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  obtain ⟨a, v, n, ha, hv, hn, hcount, horder⟩ := enumerate_total S (fun u hu => (hS u hu).1.2) hcard
  have hb := ordered_area_bound Γ p hfinite a v n hn (hS a ha).1 (fun i => (hS (v i) (hv i)).1)
    (hS a ha).2 (fun i => (hS (v i) (hv i)).2) horder
  have hc : (n : ℝ) + 2 = (S.card : ℝ) := by exact_mod_cast hcount
  rw [← hc]
  nlinarith only [hb]

end VeechDichotomy.DirichletIdealAreaBudget
