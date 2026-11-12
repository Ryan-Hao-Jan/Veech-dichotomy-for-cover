module

public import VeechDichotomy.NativeDeformationFlow
public import MNEC.NativeDifferentialEquivFlatness
public import MNEC.NativeVelocityTimeScaling
public import Mathlib.Tactic.Linarith

/-! Exact transport of embedded native directional arcs by the actual
SL2 deformation followed by a true native differential equivalence.
Coordinate speed scaling gives the actual target time interval,
maximal lifetime and injectivity, with no arc-conjugacy certificate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2ArcTransport

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) (A : SL2) (r : Differential Y)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

variable (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q A) r)

def homeomorph : Regular q ≃ₜ Regular r :=
  (NativeDeformationRegular.regularHomeomorph q A).trans (MNEC.NativeDifferentialEquiv.regularHomeomorph e)

theorem domain_clock {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u) (x : Regular q) :
    domain q v x = {t | t * k ∈ domain r u (homeomorph q A r e x)} := by
  rw [NativeDeformationFlow.domain_eq q A v x,
    MNEC.NativeDifferentialEquivFlatness.domain_eq e, hvel, MNEC.NativeVelocityTimeScaling.domain_smul r k hk u]
  rfl

theorem trajectory_clock {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u)
    (x : Regular q) (t : ℝ) (ht : t ∈ domain q v x) :
    homeomorph q A r e (trajectory q v x t) = trajectory r u (homeomorph q A r e x) (t * k) := by
  have hnew : t ∈ domain (transformed q A) (planeEquiv A v) (NativeDeformationRegular.regularHomeomorph q A x) := by
    rwa [NativeDeformationFlow.domain_eq q A v x] at ht
  have htarget : t ∈ domain r (planeEquiv A v) (homeomorph q A r e x) := by
    rwa [MNEC.NativeDifferentialEquivFlatness.domain_eq e] at hnew
  change MNEC.NativeDifferentialEquiv.regularHomeomorph e
    (NativeDeformationRegular.regularHomeomorph q A (trajectory q v x t)) = _
  rw [NativeDeformationFlow.trajectory_conjugacy q A v x t ht,
    MNEC.NativeDifferentialEquivFlatness.trajectory_conjugacy e _ _ t hnew]
  rw [hvel] at htarget ⊢
  exact MNEC.NativeVelocityTimeScaling.trajectory_smul r k hk u (homeomorph q A r e x) t htarget

theorem scaled_interval_domain {v u : Plane} {k : ℝ} (hk : 0 < k) (hvel : planeEquiv A v = k • u)
    (x : Regular q) (a b : ℝ) (hI : Icc a b ⊆ domain q v x) :
    Icc (a * k) (b * k) ⊆ domain r u (homeomorph q A r e x) := by
  intro t ht
  have hdiv : t / k ∈ Icc a b :=
    ⟨(le_div_iff₀ hk).mpr ht.1, (div_le_iff₀ hk).mpr ht.2⟩
  have hsource := hI hdiv
  rw [domain_clock q A r e hk.ne' hvel x] at hsource
  simpa only [mem_ofPred_eq, div_mul_cancel₀ _ hk.ne'] using hsource

theorem image_arc {v u : Plane} {k : ℝ} (hk : 0 < k) (hvel : planeEquiv A v = k • u)
    (x : Regular q) (a b : ℝ) (hI : Icc a b ⊆ domain q v x) :
    homeomorph q A r e '' (trajectory q v x '' Icc a b) =
      trajectory r u (homeomorph q A r e x) '' Icc (a * k) (b * k) := by
  rw [image_image]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * k, ⟨mul_le_mul_of_nonneg_right ht.1 hk.le, mul_le_mul_of_nonneg_right ht.2 hk.le⟩, ?_⟩
    exact (trajectory_clock q A r e hk.ne' hvel x t (hI ht)).symm
  · rintro ⟨t, ht, rfl⟩
    have hdiv : t / k ∈ Icc a b :=
      ⟨(le_div_iff₀ hk).mpr ht.1, (div_le_iff₀ hk).mpr ht.2⟩
    refine ⟨t / k, hdiv, ?_⟩
    simpa only [Function.comp_def, div_mul_cancel₀ _ hk.ne'] using
      trajectory_clock q A r e hk.ne' hvel x (t / k) (hI hdiv)

theorem arc_injOn {v u : Plane} {k : ℝ} (hk : 0 < k) (hvel : planeEquiv A v = k • u)
    (x : Regular q) (a b : ℝ) (hI : Icc a b ⊆ domain q v x) (hinj : InjOn (trajectory q v x) (Icc a b)) :
    InjOn (trajectory r u (homeomorph q A r e x)) (Icc (a * k) (b * k)) := by
  intro s hs t ht heq
  have hsdiv : s / k ∈ Icc a b := ⟨(le_div_iff₀ hk).mpr hs.1, (div_le_iff₀ hk).mpr hs.2⟩
  have htdiv : t / k ∈ Icc a b := ⟨(le_div_iff₀ hk).mpr ht.1, (div_le_iff₀ hk).mpr ht.2⟩
  have hpoints : homeomorph q A r e (trajectory q v x (s / k)) = homeomorph q A r e (trajectory q v x (t / k)) := by
    rw [trajectory_clock q A r e hk.ne' hvel x (s / k) (hI hsdiv),
      trajectory_clock q A r e hk.ne' hvel x (t / k) (hI htdiv), div_mul_cancel₀ _ hk.ne', div_mul_cancel₀ _ hk.ne']
    exact heq
  have hdiv := hinj hsdiv htdiv ((homeomorph q A r e).injective hpoints)
  exact (div_left_inj' hk.ne').mp hdiv

theorem preimage_arc {v u : Plane} {k : ℝ} (hk : 0 < k) (hvel : planeEquiv A v = k • u)
    (x : Regular q) (a b : ℝ) (hI : Icc a b ⊆ domain r u (homeomorph q A r e x)) :
    homeomorph q A r e ⁻¹' (trajectory r u (homeomorph q A r e x) '' Icc a b) =
      trajectory q v x '' Icc (a / k) (b / k) := by
  have hsource : Icc (a / k) (b / k) ⊆ domain q v x := by
    intro t ht
    rw [domain_clock q A r e hk.ne' hvel x]
    exact hI ⟨(div_le_iff₀ hk).mp ht.1, (le_div_iff₀ hk).mp ht.2⟩
  have himage := image_arc q A r e hk hvel x (a / k) (b / k) hsource
  rw [div_mul_cancel₀ _ hk.ne', div_mul_cancel₀ _ hk.ne'] at himage
  have hp := congrArg (fun S => homeomorph q A r e ⁻¹' S) himage
  simpa only [preimage_image_eq _ (homeomorph q A r e).injective] using hp.symm

end VeechDichotomy.NativeSL2ArcTransport
