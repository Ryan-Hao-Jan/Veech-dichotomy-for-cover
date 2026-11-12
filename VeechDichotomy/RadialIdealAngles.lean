module

public import VeechDichotomy.RadialPolygonOrder
public import VeechDichotomy.FiniteEndpointAngleLimits

/-! Every actual corner angle, and hence the entire actual corner-angle
sum, of a radially approximated ideal polygon tends to zero. The ideal
vertices are distinct finite endpoints in their constructed cyclic order. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RadialIdealAngles

open Filter Topology IdealBoundaryCoordinates IdealRadialLimits RadialPolygonOrder
open HyperbolicIntrinsicAngles HyperbolicPolygonAngles
open scoped UpperHalfPlane

theorem angle_tendsto_zero (p : ℍ) (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (haI : a ≠ Complex.I) (hbI : b ≠ Complex.I) (hcI : c ≠ Complex.I) (hba : b ≠ a) (hca : c ≠ a) :
    Tendsto (fun k => angleAt (approx p a ha k) (approx p b hb k) (approx p c hc k)) atTop (𝓝 0) := by
  exact FiniteEndpointAngleLimits.angleAt_tendsto_zero _ _ _ _ _ _
    (re_tendsto p a ha haI) (re_tendsto p b hb hbI) (re_tendsto p c hc hcI)
    (im_tendsto p a ha haI) (im_tendsto p b hb hbI) (im_tendsto p c hc hcI)
    (fun he => hba (endpoint_injective hb ha hbI haI he))
    (fun he => hca (endpoint_injective hc ha hcI haI he))

theorem polygonAngleSum_tendsto_zero (p : ℍ) (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (ha : ‖a‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (haI : a ≠ Complex.I) (hvI : ∀ i, v i ≠ Complex.I)
    (h : PlanarPolygonAngles.StrictlyOrdered a v n) :
    Tendsto (fun k => polygonAngleSum (approx p a ha k) (fun i => approx p (v i) (hv i) k) n)
      atTop (𝓝 0) := by
  have hr := angle_tendsto_zero p a (v 0) (v n) ha (hv 0) (hv n) haI (hvI 0) (hvI n)
    (root_ne hn h 0 (Nat.zero_le n)).symm (root_ne hn h n le_rfl).symm
  have hf := angle_tendsto_zero p (v 0) a (v 1) (hv 0) ha (hv 1) (hvI 0) haI (hvI 1)
    (root_ne hn h 0 (Nat.zero_le n)) (chain_ne h (by omega : 1 ≠ 0) (by omega) (Nat.zero_le n))
  have hm (i : ℕ) (hi : i ∈ Finset.range (n - 1)) :
      Tendsto (fun k => angleAt (approx p (v (i + 1)) (hv (i + 1)) k)
        (approx p (v i) (hv i) k) (approx p (v (i + 2)) (hv (i + 2)) k)) atTop (𝓝 0) := by
    have hi' := Finset.mem_range.mp hi
    exact angle_tendsto_zero p (v (i + 1)) (v i) (v (i + 2)) (hv _) (hv _) (hv _)
      (hvI _) (hvI _) (hvI _)
      (chain_ne h (by omega : i ≠ i + 1) (by omega) (by omega))
      (chain_ne h (by omega : i + 2 ≠ i + 1) (by omega) (by omega))
  have hsum := tendsto_finsetSum (a := fun _ : ℕ => (0 : ℝ)) (Finset.range (n - 1)) hm
  have hl := angle_tendsto_zero p (v n) a (v (n - 1)) (hv n) ha (hv _) (hvI n) haI (hvI _)
    (root_ne hn h n le_rfl) (chain_ne h (by omega : n - 1 ≠ n) (by omega) le_rfl)
  simpa only [polygonAngleSum, Finset.sum_const_zero, add_zero] using! ((hr.add hf).add hsum).add hl

end VeechDichotomy.RadialIdealAngles
