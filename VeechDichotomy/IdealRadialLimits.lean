module

public import VeechDichotomy.IdealBoundaryCoordinates
public import VeechDichotomy.NormalizedIdealTriangleExhaustion

/-! Actual upper-half-plane radial approximations to every finite ideal
endpoint, including the limits of their real and imaginary coordinates. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealRadialLimits

open Set Filter Topology DirichletIdealRadialPoints IdealBoundaryCoordinates
open HyperbolicKleinHomeomorph
open scoped UpperHalfPlane

def time (n : ℕ) : ℝ := NormalizedIdealTriangleExhaustion.cutoff (n + 1)

theorem time_pos (n : ℕ) : 0 < time n := by
  have h := NormalizedIdealTriangleExhaustion.cutoff_monotone (show 1 ≤ n + 1 by omega)
  have hone : 0 < NormalizedIdealTriangleExhaustion.cutoff 1 := by
    norm_num [NormalizedIdealTriangleExhaustion.cutoff]
  exact lt_of_lt_of_le hone h

theorem time_lt_one (n : ℕ) : time n < 1 := NormalizedIdealTriangleExhaustion.cutoff_lt_one _

theorem time_tendsto : Tendsto time atTop (𝓝 1) :=
  NormalizedIdealTriangleExhaustion.cutoff_tendsto.comp (tendsto_add_atTop_nat 1)

def approx (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (n : ℕ) : ℍ :=
  radialPoint p u hu (time n) (time_pos n).le (time_lt_one n)

theorem point_approx (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (n : ℕ) :
    HyperbolicKleinMap.point (approx p u hu n) = radial p u (time n) :=
  point_radialPoint _ _ _ _ _ _

theorem approx_mem_region (Γ : Subgroup LinearGroup.SL2) (p : ℍ) {u : ℂ}
    (hu : u ∈ idealBoundary Γ p) (n : ℕ) : approx p u hu.2 n ∈ HyperbolicDirichletRegions.region Γ p :=
  radialPoint_mem_region Γ p hu _ _ _

theorem radial_tendsto (p : ℍ) (u : ℂ) :
    Tendsto (fun n => radial p u (time n)) atTop (𝓝 u) :=
  (tendsto_radial_at_one p u).comp time_tendsto

theorem re_tendsto (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) :
    Tendsto (fun n => (approx p u hu n).re) atTop (𝓝 (endpoint u)) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp (radial_tendsto p u)
  have hi := Complex.continuous_im.continuousAt.tendsto.comp (radial_tendsto p u)
  exact hr.div (tendsto_const_nhds.sub hi) (denominator_pos hu hI).ne'

theorem im_tendsto (p : ℍ) (u : ℂ) (hu : ‖u‖ = 1) (hI : u ≠ Complex.I) :
    Tendsto (fun n => (approx p u hu n).im) atTop (𝓝 0) := by
  have hi := Complex.continuous_im.continuousAt.tendsto.comp (radial_tendsto p u)
  have hs := Complex.continuous_normSq.continuousAt.tendsto.comp (radial_tendsto p u)
  have hg : Tendsto (fun n => 1 - Complex.normSq (radial p u (time n))) atTop (𝓝 0) := by
    simpa only [normSq_eq_one hu, sub_self] using! (tendsto_const_nhds (x := (1 : ℝ))).sub hs
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hg
  simpa only [Real.sqrt_zero, zero_div] using!
    hroot.div (tendsto_const_nhds.sub hi) (denominator_pos hu hI).ne'

end VeechDichotomy.IdealRadialLimits
