module

public import VeechDichotomy.HyperbolicDirichletLocalFiniteness
public import Mathlib.Topology.LocallyFinite

/-! Genuine Dirichlet tiles form a locally finite closed cover of the
hyperbolic plane for any discrete SL2 subgroup. A tile meeting a compact
set has its actual center in one bounded hyperbolic ball, so proper
discontinuity leaves only finitely many such tiles. This is the actual
local tessellation argument, not an assumed polygon/cycle interface. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletTessellation

open LinearGroup HyperbolicDirichletRegions HyperbolicDirichletLocalFiniteness Set Topology
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2)

def tile (p : ℍ) (γ : Γ) : Set ℍ := (fun z : ℍ => γ • z) '' region Γ p

theorem tile_closed (p : ℍ) (γ : Γ) : IsClosed (tile Γ p γ) :=
  (Homeomorph.smul γ : ℍ ≃ₜ ℍ).isClosedMap _ (isClosed_region Γ p)

theorem center_bound (p z : ℍ) (γ : Γ) (hz : z ∈ region Γ p) :
    dist p (γ • p) ≤ 2 * dist p (γ • z) := by
  have hd := hz γ⁻¹
  change dist z p ≤ dist z ((γ : SL2)⁻¹ • p) at hd
  have hm : dist z ((γ : SL2)⁻¹ • p) = dist p ((γ : SL2) • z) := by
    calc
      dist z ((γ : SL2)⁻¹ • p) = dist ((γ : SL2) • z) p := by
        simpa only [smul_inv_smul] using (dist_smul (γ : SL2) z ((γ : SL2)⁻¹ • p)).symm
      _ = dist p ((γ : SL2) • z) := dist_comm _ _
  rw [hm] at hd
  change dist p ((γ : SL2) • p) ≤ 2 * dist p ((γ : SL2) • z)
  calc
    dist p ((γ : SL2) • p) ≤ dist p ((γ : SL2) • z) + dist ((γ : SL2) • z) ((γ : SL2) • p) :=
      dist_triangle _ _ _
    _ = dist p ((γ : SL2) • z) + dist z p := by rw [dist_smul]
    _ ≤ dist p ((γ : SL2) • z) + dist p ((γ : SL2) • z) := by linarith only [hd]
    _ = 2 * dist p ((γ : SL2) • z) := by ring

variable [DiscreteTopology Γ]

theorem finite_inter_compact (p : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    {γ : Γ | (tile Γ p γ ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
  have hf : {γ : Γ | γ • p ∈ Metric.closedBall p (2 * R)}.Finite :=
    finite_orbit_in_compact Γ p (isCompact_closedBall _ _)
  apply hf.subset
  intro γ hγ
  obtain ⟨w, ⟨z, hz, hzw⟩, hwK⟩ := hγ
  change γ • z = w at hzw
  change dist (γ • p) p ≤ 2 * R
  rw [dist_comm]
  have hw : dist p w ≤ R := by
    have h := Metric.mem_closedBall.mp (hR hwK)
    rwa [dist_comm] at h
  calc
    dist p (γ • p) ≤ 2 * dist p (γ • z) := center_bound Γ p z γ hz
    _ = 2 * dist p w := by rw [hzw]
    _ ≤ 2 * R := mul_le_mul_of_nonneg_left hw (by norm_num)

theorem locallyFinite_tiles (p : ℍ) : LocallyFinite (tile Γ p) := by
  intro x
  exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num),
    finite_inter_compact Γ p (isCompact_closedBall _ _)⟩

theorem tiles_cover (p : ℍ) : (⋃ γ : Γ, tile Γ p γ) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨γ, hγ⟩ := exists_translate_mem Γ p z
  exact ⟨γ⁻¹, γ • z, hγ, inv_smul_smul γ z⟩

end VeechDichotomy.HyperbolicDirichletTessellation
