module

public import VeechDichotomy.DirichletVerticalStripBounds
public import VeechDichotomy.DirichletUpperEndConstraints
public import Mathlib.Topology.Order.IntermediateValue

/-! Near the actual ideal endpoint at physical infinity, an actual
regular-center native lattice Dirichlet region is exactly a vertical
strip of strictly positive finite width above a finite height. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletUpperStrips

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicBisectorNull HyperbolicDistanceComparison DirichletIdealRadialPoints
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def verticalSlice (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ) : Set ℝ :=
  {x | ∀ γ ∈ S, leading p (γ • p) = 0 → linear p (γ • p) * x + constant p (γ • p) ≤ 0}

theorem isClosed_verticalSlice (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ) : IsClosed (verticalSlice Γ p S) := by
  have he : verticalSlice Γ p S = ⋂ γ ∈ S, ⋂ (_ : leading p (γ • p) = 0),
      {x : ℝ | linear p (γ • p) * x + constant p (γ • p) ≤ 0} := by ext x; simp [verticalSlice]
  rw [he]
  apply isClosed_iInter
  intro γ
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_le (by fun_prop) continuous_const

theorem convex_verticalSlice (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ) : Convex ℝ (verticalSlice Γ p S) := by
  intro x hx y hy a b ha hb hab γ hγ hA
  change linear p (γ • p) * (a * x + b * y) + constant p (γ • p) ≤ 0
  calc
    _ = a * (linear p (γ • p) * x + constant p (γ • p)) +
        b * (linear p (γ • p) * y + constant p (γ • p)) := by
      linear_combination -constant p (γ • p) * hab
    _ ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx γ hγ hA))
      (mul_nonpos_of_nonneg_of_nonpos hb (hy γ hγ hA))

theorem mem_slice_of_mem_region (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ) {z : ℍ} (hz : z ∈ region Γ p) :
    z.re ∈ verticalSlice Γ p S := by
  intro γ _ hA
  have hf := (HyperbolicDistanceComparison.dist_le_iff p (γ • p) z).mp (hz γ)
  simpa only [form, hA, zero_mul, zero_add, UpperHalfPlane.coe_re] using hf

def atHeight (y : ℝ) (hy : 0 < y) (x : ℝ) : ℍ := ⟨⟨x, y⟩, hy⟩

theorem continuous_atHeight (y : ℝ) (hy : 0 < y) : Continuous (atHeight y hy) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ))
  have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  rw [he]
  fun_prop

theorem center_interior_slice (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) (S : Finset Γ) :
    p.re ∈ interior (verticalSlice Γ p S) := by
  have he : atHeight p.im p.im_pos p.re = p := UpperHalfPlane.ext_re_im rfl rfl
  have hl : Tendsto (atHeight p.im p.im_pos) (𝓝 p.re) (𝓝 p) := by
    simpa only [he] using! ((continuous_atHeight p.im p.im_pos).continuousAt (x := p.re)).tendsto
  have hd : region Γ p ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp (DirichletInteriorDensity.center_interior Γ p)
  have hev : ∀ᶠ x in 𝓝 p.re, atHeight p.im p.im_pos x ∈ region Γ p := hl.eventually hd
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hev] with x hx
  exact mem_slice_of_mem_region Γ p S hx

theorem exists_upper_strip (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) :
    ∃ a b H : ℝ, a < p.re ∧ p.re < b ∧ 0 < H ∧
      ∀ z : ℍ, H ≤ z.im → (z ∈ region Γ p ↔ z.re ∈ Icc a b) := by
  let : DiscreteTopology Γ := hΓ.1
  obtain ⟨S, H, hH, hhigh⟩ := DirichletUpperEndConstraints.exists_upper_constraints Γ hΓ p hp hI
  obtain ⟨a, b, _, _, hbound⟩ := DirichletVerticalStripBounds.exists_bounds Γ hΓ p hp hI
  let V := verticalSlice Γ p S
  have hVbound : V ⊆ Icc a b := by
    intro x hx
    let z := atHeight H hH x
    have hz : z ∈ region Γ p := (hhigh z le_rfl).mpr hx
    exact hbound z hz
  have hlo : BddBelow V := ⟨a, fun _ hx => (hVbound hx).1⟩
  have hhi : BddAbove V := ⟨b, fun _ hx => (hVbound hx).2⟩
  have hint : p.re ∈ interior V := center_interior_slice Γ p S
  have hc : IsConnected V := ⟨⟨p.re, interior_subset hint⟩, (convex_verticalSlice Γ p S).isPreconnected⟩
  have heq : V = Icc (sInf V) (sSup V) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed hc hlo hhi (isClosed_verticalSlice Γ p S)
  have hmid : sInf V < p.re ∧ p.re < sSup V := by
    have hint' : p.re ∈ interior (Icc (sInf V) (sSup V)) := by rw [← heq]; exact hint
    simpa only [interior_Icc, mem_Ioo] using hint'
  refine ⟨sInf V, sSup V, H, hmid.1, hmid.2, hH, ?_⟩
  intro z hz
  have ht : z ∈ region Γ p ↔ z.re ∈ V := hhigh z hz
  rwa [heq] at ht

end VeechDichotomy.DirichletUpperStrips
