module

public import VeechDichotomy.HyperbolicKleinDirichlet
public import Mathlib.Topology.Connected.PathConnected

/-! Actual continuous segments obtained by lifting straight Klein-disk
chords through the proved homeomorphism. They have the literal prescribed
endpoints and stay in every genuine ordinary or strict Dirichlet region
containing their endpoints. This constructs actual region paths rather
than assuming a geodesic/convexity interface. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinSegments

open LinearGroup HyperbolicKleinMap HyperbolicKleinHomeomorph HyperbolicKleinDirichlet
open HyperbolicDirichletRegions HyperbolicStrictDirichlet Set Topology
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

def chord (a b : ℍ) (t : I) : ℂ := (1 - t.val) • point a + t.val • point b

theorem chord_mem_ball (a b : ℍ) (t : I) : chord a b t ∈ Metric.ball (0 : ℂ) 1 := by
  have ha : point a ∈ Metric.ball (0 : ℂ) 1 := by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one a
  have hb : point b ∈ Metric.ball (0 : ℂ) 1 := by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one b
  change (1 - t.val) • point a + t.val • point b ∈ Metric.ball (0 : ℂ) 1
  exact (convex_ball _ _) ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

def chordPoint (a b : ℍ) (t : I) : Disk :=
  ⟨chord a b t, by simpa only [Metric.mem_ball, dist_zero_right] using chord_mem_ball a b t⟩

def interpolate (a b : ℍ) (t : I) : ℍ := inverse (chordPoint a b t)

theorem continuous_chord (a b : ℍ) : Continuous (chord a b) := by
  have ht : Continuous (Subtype.val : I → ℝ) := continuous_subtype_val
  exact ((continuous_const.sub ht).smul continuous_const).add (ht.smul continuous_const)

theorem continuous_interpolate (a b : ℍ) : Continuous (interpolate a b) :=
  continuous_inverse.comp ((continuous_chord a b).subtype_mk _)

@[simp] theorem chordPoint_zero (a b : ℍ) : chordPoint a b 0 = forward a := by
  apply Subtype.ext
  simp [chordPoint, chord, forward]

@[simp] theorem chordPoint_one (a b : ℍ) : chordPoint a b 1 = forward b := by
  apply Subtype.ext
  simp [chordPoint, chord, forward]

@[simp] theorem interpolate_zero (a b : ℍ) : interpolate a b 0 = a := by
  rw [interpolate, chordPoint_zero, inverse_forward]

@[simp] theorem interpolate_one (a b : ℍ) : interpolate a b 1 = b := by
  rw [interpolate, chordPoint_one, inverse_forward]

def path (a b : ℍ) : Path a b where
  toFun := interpolate a b
  continuous_toFun := continuous_interpolate a b
  source' := interpolate_zero a b
  target' := interpolate_one a b

theorem point_interpolate (a b : ℍ) (t : I) : point (interpolate a b t) = chord a b t :=
  congrArg Subtype.val (forward_inverse (chordPoint a b t))

theorem interpolate_mem_region (Γ : Subgroup SL2) (p a b : ℍ)
    (ha : a ∈ region Γ p) (hb : b ∈ region Γ p) (t : I) : interpolate a b t ∈ region Γ p := by
  have ha' : point a ∈ diskRegion Γ p := by rw [← image_region]; exact ⟨a, ha, rfl⟩
  have hb' : point b ∈ diskRegion Γ p := by rw [← image_region]; exact ⟨b, hb, rfl⟩
  have hc : chord a b t ∈ diskRegion Γ p :=
    (convex_diskRegion Γ p) ha' hb' (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  intro γ
  apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) (interpolate a b t)).mpr
  rw [point_interpolate]
  exact mem_iInter.mp hc.2 γ

theorem interpolate_mem_strictRegion (Γ : Subgroup SL2) (p a b : ℍ)
    (ha : a ∈ strictRegion Γ p) (hb : b ∈ strictRegion Γ p) (t : I) : interpolate a b t ∈ strictRegion Γ p := by
  have ha' : point a ∈ strictDiskRegion Γ p := by rw [← image_strictRegion]; exact ⟨a, ha, rfl⟩
  have hb' : point b ∈ strictDiskRegion Γ p := by rw [← image_strictRegion]; exact ⟨b, hb, rfl⟩
  have hc : chord a b t ∈ strictDiskRegion Γ p :=
    (convex_strictDiskRegion Γ p) ha' hb' (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  intro γ hγ
  apply (HyperbolicKleinHalfPlanes.dist_lt_iff p (γ • p) (interpolate a b t)).mpr
  rw [point_interpolate]
  exact mem_iInter.mp hc.2 (⟨γ, hγ⟩ : {γ : Γ | γ • p ≠ p})

theorem region_isPathConnected (Γ : Subgroup SL2) (p : ℍ) : IsPathConnected (region Γ p) := by
  refine ⟨p, center_mem Γ p, ?_⟩
  intro y hy
  exact ⟨path p y, fun t => interpolate_mem_region Γ p p y (center_mem Γ p) hy t⟩

theorem strictRegion_isPathConnected (Γ : Subgroup SL2) (p : ℍ) : IsPathConnected (strictRegion Γ p) := by
  have hp : p ∈ strictRegion Γ p := fun γ hγ => by
    rw [dist_self]
    exact dist_pos.mpr hγ.symm
  refine ⟨p, hp, ?_⟩
  intro y hy
  exact ⟨path p y, fun t => interpolate_mem_strictRegion Γ p p y hp hy t⟩

end VeechDichotomy.HyperbolicKleinSegments
