module

public import VeechDichotomy.RegularCenterOrbitTransport
public import VeechDichotomy.DirichletVerticalStripBounds

/-! At an actual ideal Dirichlet endpoint at infinity there are
infinitely many actual orbit centers of maximal height. Every one has
another maximal-height orbit center strictly to its right. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.MaximalHeightCenters

open LinearGroup Set HyperbolicRegularCenters DirichletIdealRadialPoints DirichletIdealInfinity
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def centers (Γ : Subgroup SL2) (p : ℍ) : Set ℍ := {q | q ∈ MulAction.orbit Γ p ∧ q.im = p.im}

theorem base_mem (Γ : Subgroup SL2) (p : ℍ) : p ∈ centers Γ p := ⟨⟨1, one_smul Γ p⟩, rfl⟩

theorem ideal_at_center (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    {q : ℍ} (hq : q ∈ centers Γ p) : Complex.I ∈ idealBoundary Γ q := by
  obtain ⟨γ, hγ⟩ := hq.1
  apply (mem_ideal_iff Γ q).mpr
  intro δ
  have hh := orbit_height_le Γ p hI (δ * γ)
  simpa only [mul_smul, hγ, ← hq.2] using! hh

theorem regular_at_center (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p)
    {q : ℍ} (hq : q ∈ centers Γ p) : RegularCenter Γ q := by
  obtain ⟨γ, rfl⟩ := hq.1
  exact RegularCenterOrbitTransport.smul_regular Γ p hp γ

theorem exists_larger (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) {q : ℍ} (hq : q ∈ centers Γ p) :
    ∃ r ∈ centers Γ p, q.re < r.re := by
  obtain ⟨_, δ, _, _, hA, hB⟩ := DirichletVerticalEndBounds.exists_vertical_pair Γ hΓ q
    (regular_at_center Γ p hp hq) (ideal_at_center Γ p hI hq)
  have him : (δ • q).im = q.im := sub_eq_zero.mp hA
  have hdiff : 0 < (δ • q).re - q.re := by
    rw [DirichletVerticalStripBounds.linear_vertical q (δ • q) hA] at hB
    exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) q.im_pos)).mp hB
  refine ⟨δ • q, ⟨?_, him.trans hq.2⟩, sub_pos.mp hdiff⟩
  obtain ⟨γ, hγ⟩ := hq.1
  refine ⟨δ * γ, ?_⟩
  change (δ * γ) • p = δ • q
  change γ • p = q at hγ
  rw [mul_smul, hγ]

theorem centers_infinite (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) : (centers Γ p).Infinite := by
  classical
  intro hf
  have hnonempty : hf.toFinset.Nonempty := ⟨p, hf.mem_toFinset.mpr (base_mem Γ p)⟩
  obtain ⟨q, hq, hmax⟩ := hf.toFinset.exists_max_image (fun z : ℍ => z.re) hnonempty
  obtain ⟨r, hr, hlt⟩ := exists_larger Γ hΓ p hp hI (hf.mem_toFinset.mp hq)
  exact not_lt_of_ge (hmax r (hf.mem_toFinset.mpr hr)) hlt

end VeechDichotomy.MaximalHeightCenters
