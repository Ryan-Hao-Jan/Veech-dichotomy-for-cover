module

public import VeechDichotomy.KleinRowSeparation
public import VeechDichotomy.DirichletClosedSubsetCompactness
public import VeechDichotomy.NativeCompatibleHoroballs

/-! The complement of the actual constructed normalized cusp
horoballs in the actual Dirichlet region is genuinely compact. Each
actual ideal endpoint is excluded by an explicit Klein functional. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCuspCompactCore

open LinearGroup Set HyperbolicRegularCenters HyperbolicDirichletRegions HyperbolicKleinMap
open DirichletIdealRadialPoints NativeFiniteCuspCharts NativeLatticeConjugation
open IdealEndpointHeightNormalization ConjugatedHyperbolicActions
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def core (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (R : ℝ) : Set ℍ :=
  region Γ p \ ⋃ u : idealBoundary Γ p, RelativeIdealHoroballs.horoball p (chart Γ hΓ p hp u).matrix R

theorem isClosed_core (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (R : ℝ) :
    IsClosed (core Γ hΓ p hp R) :=
  (isClosed_region Γ p).inter
    (isOpen_iUnion (fun u => RelativeIdealHoroballs.isOpen_horoball p (chart Γ hΓ p hp u).matrix R)).isClosed_compl

theorem excludes_ideal (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (R : ℝ)
    (u : idealBoundary Γ p) : u.val ∉ closure (point '' core Γ hΓ p hp R) := by
  let B := (chart Γ hΓ p hp u).matrix
  have hBI : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p := by
    rw [(chart Γ hΓ p hp u).endpoint_eq]
    exact u.property
  obtain ⟨a, b, _, _, hbounds⟩ := DirichletVerticalStripBounds.exists_bounds (conjugate Γ B)
    (isLattice_conjugate Γ hΓ B) (B • p) (regular_conjugate Γ p hp B) (ideal_conjugate Γ p B hBI)
  have hr (z : ℍ) (hz : z ∈ core Γ hΓ p hp R) : |(B • z).re| ≤ |a| + |b| + 1 := by
    have hw := hbounds (B • z) ((mem_region_iff Γ B p z).mpr hz.1)
    apply abs_le.mpr
    constructor
    · linarith only [hw.1, neg_abs_le a, abs_nonneg b]
    · linarith only [hw.2, le_abs_self b, abs_nonneg a]
  have hi (z : ℍ) (hz : z ∈ core Γ hΓ p hp R) : (B • z).im ≤ R * (B • p).im := by
    apply le_of_not_gt
    intro hlt
    exact hz.2 (mem_iUnion.mpr ⟨u, hlt⟩)
  have he := KleinRowSeparation.endpoint_not_mem_closure B (core Γ hΓ p hp R) (|a| + |b| + 1)
    (R * (B • p).im) hr hi
  rwa [(chart Γ hΓ p hp u).endpoint_eq] at he

theorem isCompact_core (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (R : ℝ) :
    IsCompact (core Γ hΓ p hp R) := by
  apply DirichletClosedSubsetCompactness.compact_of_ideal_avoiding Γ p _ (isClosed_core Γ hΓ p hp R)
    (fun _ hz => hz.1)
  intro u hu
  exact excludes_ideal Γ hΓ p hp R ⟨u, hu⟩

end VeechDichotomy.NativeCuspCompactCore
