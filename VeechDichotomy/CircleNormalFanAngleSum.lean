module

public import VeechDichotomy.OrderedNormalFanWidths

/-! The actual normal-cone angular widths of any finite set of at
least two distinct equal-radius nonzero complex sites sum to 2*pi.
The two-site case is two genuine half-planes. Otherwise the actual
circle polygon enumeration and proved exterior-angle identity apply. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircleNormalFanAngleSum

open Set HyperbolicRegionAngles FiniteSiteNormalFans

theorem pair_sector_left (a b : ℂ) : sector ({a, b} : Set ℂ) a = DualConeAngleWidth.halfPlane (b - a) := by
  ext u
  simp [sector, functional_apply, DualConeAngleWidth.halfPlane]

theorem pair_sector_right (a b : ℂ) : sector ({a, b} : Set ℂ) b = DualConeAngleWidth.halfPlane (a - b) := by
  ext u
  simp [sector, functional_apply, DualConeAngleWidth.halfPlane]

theorem pair_sum (a b : ℂ) (hab : a ≠ b) :
    (∑ s ∈ ({a, b} : Finset ℂ), vectorWidth (sector ({a, b} : Set ℂ) s)) = 2 * Real.pi := by
  classical
  rw [Finset.sum_pair hab, pair_sector_left, pair_sector_right,
    DualConeAngleWidth.width_halfPlane (b - a) (sub_ne_zero.mpr hab.symm),
    DualConeAngleWidth.width_halfPlane (a - b) (sub_ne_zero.mpr hab)]
  ring

theorem sum_widths (S : Finset ℂ) (R : ℝ) (hR : 0 < R) (hS : ∀ z ∈ S, ‖z‖ = R) (hcard : 2 ≤ S.card) :
    (∑ s ∈ S, vectorWidth (sector (S : Set ℂ) s)) = 2 * Real.pi := by
  classical
  by_cases htwo : S.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
    simpa only [Finset.coe_pair] using pair_sum a b hab
  · have hthree : 3 ≤ S.card := by omega
    obtain ⟨a, v, n, _, hn, _, hvertices, hstrict⟩ := CirclePolygonOrder.enumerate S R hR hS hthree
    have hsum := OrderedNormalFanWidths.sum_widths a v n hn hstrict
    rw [PlanarPolygonVertexSums.vertexFinset_eq hvertices, hvertices] at hsum
    exact hsum

theorem sum_widths_fintype (V : Set ℂ) [Fintype V] (R : ℝ) (hR : 0 < R)
    (hV : ∀ z ∈ V, ‖z‖ = R) (hcard : 2 ≤ Fintype.card V) :
    (∑ s : V, vectorWidth (sector V s.val)) = 2 * Real.pi := by
  classical
  have he : (∑ s : V, vectorWidth (sector V s.val)) =
      ∑ s ∈ V.toFinset, vectorWidth (sector V s) :=
    Finset.sum_set_coe (f := fun s : ℂ => vectorWidth (sector V s)) V
  rw [he]
  have hsum := sum_widths V.toFinset R hR (fun z hz => hV z (Set.mem_toFinset.mp hz))
    (by simpa only [Set.toFinset_card] using hcard)
  simpa only [Set.coe_toFinset] using hsum

end VeechDichotomy.CircleNormalFanAngleSum
