module

public import VeechDichotomy.DirichletNearestSiteCones
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Genuine normal cones of an actual finite complex site set form a
closed convex fan covering the plane, with pairwise disjoint interiors
at distinct sites. The cover comes from an actual finite maximum of
linear functionals; strict interior signs use a genuine open linear map. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteSiteNormalFans

open Set Topology

def functional (s t : ℂ) : ℂ →L[ℝ] ℝ := InnerProductSpace.toDual ℝ ℂ (t - s)
def sector (V : Set ℂ) (s : ℂ) : Set ℂ := {u | ∀ t ∈ V, functional s t u ≤ 0}

theorem functional_apply (s t u : ℂ) : functional s t u = inner ℝ (t - s) u := rfl

theorem isClosed_sector (V : Set ℂ) (s : ℂ) : IsClosed (sector V s) := by
  have he : sector V s = ⋂ t : V, {u : ℂ | functional s t.val u ≤ 0} := by ext u; simp [sector]
  rw [he]
  exact isClosed_iInter (fun t => isClosed_le (functional s t.val).continuous continuous_const)

theorem convex_sector (V : Set ℂ) (s : ℂ) : Convex ℝ (sector V s) := by
  have he : sector V s = ⋂ t : V, {u : ℂ | functional s t.val u ≤ 0} := by ext u; simp [sector]
  rw [he]
  exact convex_iInter (fun t => (convex_Iic (0 : ℝ)).linear_preimage (functional s t.val).toLinearMap)

theorem exists_sector (V : Set ℂ) (hV : V.Finite) (hne : V.Nonempty) (u : ℂ) : ∃ s ∈ V, u ∈ sector V s := by
  classical
  have hf : hV.toFinset.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨s, hV.mem_toFinset.mpr hs⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image hV.toFinset (fun s : ℂ => inner ℝ s u) hf
  refine ⟨s, hV.mem_toFinset.mp hs, ?_⟩
  intro t ht
  have h := hmax t (hV.mem_toFinset.mpr ht)
  rw [functional_apply, inner_sub_left]
  linarith

theorem sectors_cover (V : Set ℂ) (hV : V.Finite) (hne : V.Nonempty) : (⋃ s ∈ V, sector V s) = univ := by
  ext u
  simp only [mem_iUnion, mem_univ, iff_true, exists_prop]
  exact exists_sector V hV hne u

theorem interior_strict {V : Set ℂ} {s t u : ℂ} (ht : t ∈ V) (hst : s ≠ t) (hu : u ∈ interior (sector V s)) :
    functional s t u < 0 := by
  let L := functional s t
  have hvec : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  have hnon : L (t - s) ≠ 0 := (real_inner_self_pos.mpr hvec).ne'
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨(y / L (t - s)) • (t - s), ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hnon]
  have hopen : IsOpenMap L := L.isOpenMap hsurj
  have hsub : sector V s ⊆ L ⁻¹' Iic (0 : ℝ) := fun _ hv => hv t ht
  have hi : u ∈ interior (L ⁻¹' Iic (0 : ℝ)) := interior_mono hsub hu
  rw [← hopen.preimage_interior_eq_interior_preimage L.continuous, interior_Iic] at hi
  exact hi

theorem disjoint_interiors {V : Set ℂ} {s t : ℂ} (hs : s ∈ V) (ht : t ∈ V) (hst : s ≠ t) :
    Disjoint (interior (sector V s)) (interior (sector V t)) := by
  apply disjoint_left.mpr
  intro u hus hut
  have h₁ := interior_strict ht hst hus
  have h₂ := interior_strict hs hst.symm hut
  rw [functional_apply] at h₁ h₂
  rw [show s - t = -(t - s) by abel, inner_neg_left] at h₂
  linarith

end VeechDichotomy.FiniteSiteNormalFans
