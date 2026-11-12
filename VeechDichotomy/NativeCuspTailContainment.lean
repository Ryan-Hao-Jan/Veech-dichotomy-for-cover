module

public import VeechDichotomy.NativeCompatibleHoroballs
public import VeechDichotomy.ConnectedOpenFamilies

/-! At the actual common compatible cusp depth, a continuous actual
half-plane path whose tail is covered by actual cusp horoballs remains
in one actual translate. The eventual-cover statement itself still
requires the compact cusp-core theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCuspTailContainment

open LinearGroup Set HyperbolicRegularCenters DirichletIdealRadialPoints NativeCompatibleHoroballs
open scoped UpperHalfPlane

theorem tail_contained (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (R : ℝ)
    (hpair : ∀ u v : idealBoundary Γ p, ∀ γ δ : Γ,
      tile Γ hΓ p hp R u γ = tile Γ hΓ p hp R v δ ∨
        Disjoint (tile Γ hΓ p hp R u γ) (tile Γ hΓ p hp R v δ))
    (f : ℝ → ℍ) (hf : Continuous f) (T : ℝ)
    (hcover : ∀ t : ℝ, T ≤ t → ∃ (u : idealBoundary Γ p) (γ : Γ), f t ∈ tile Γ hΓ p hp R u γ) :
    ∃ (u : idealBoundary Γ p) (γ : Γ), ∀ t : ℝ, T ≤ t → f t ∈ tile Γ hΓ p hp R u γ := by
  let U : (idealBoundary Γ p × Γ) → Set ℍ := fun i => tile Γ hΓ p hp R i.1 i.2
  have hopen : ∀ i, IsOpen (U i) := fun i => isOpen_tile Γ hΓ p hp R i.1 i.2
  have hpairs : ∀ i j, U i = U j ∨ Disjoint (U i) (U j) := fun i j => hpair i.1 j.1 i.2 j.2
  have hpre : IsPreconnected (f '' Ici T) := (convex_Ici T).isPreconnected.image f hf.continuousOn
  have hsub : f '' Ici T ⊆ ⋃ i, U i := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, γ, hm⟩ := hcover t ht
    exact mem_iUnion.mpr ⟨(u, γ), hm⟩
  obtain ⟨j, hj⟩ := ConnectedOpenFamilies.exists_container U hopen hpairs hpre ⟨f T, T, le_rfl, rfl⟩ hsub
  exact ⟨j.1, j.2, fun t ht => hj ⟨t, ht, rfl⟩⟩

end VeechDichotomy.NativeCuspTailContainment
