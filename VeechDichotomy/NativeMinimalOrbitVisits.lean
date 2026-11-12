module

public import VeechDichotomy.NativePeriodicOrbits
public import VeechDichotomy.BoundedCountRates
public import Mathlib.Data.Set.Card

/-! Complete minimal native orbits are injective: a collision would
give a nonzero period, contradicting the proved compact/null periodic
orbit obstruction to density. Thus geometric intersection counts are
actual visit-time counts on these source orbits. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeMinimalOrbitVisits

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

theorem trajectory_injective (hmin : NativeDynamics.MinimalDirection q v) (x : CompleteOrbits q v) :
    Function.Injective (trajectory q v x.val) := by
  intro s t hst
  by_contra hne
  have htime : timeMap q v s x = timeMap q v t x := Subtype.ext hst
  have hperiod : timeMap q v (s - t) x = x := by
    calc
      timeMap q v (s - t) x = timeMap q v (-t) (timeMap q v s x) := by
        rw [← timeMap_add]
        congr 1
        ring
      _ = timeMap q v (-t) (timeMap q v t x) := congrArg (timeMap q v (-t)) htime
      _ = x := timeMap_neg_timeMap q v t x
  exact NativePeriodicOrbits.periodic_orbit_not_dense q v hmin.1 x (sub_ne_zero.mpr hne) hperiod (hmin.2 x)

def visits (x : CompleteOrbits q v) (S : Set (Regular q)) (a b : ℝ) : Set ℝ :=
  trajectory q v x.val ⁻¹' S ∩ Icc a b

theorem intersection_eq_image (x : CompleteOrbits q v) (S : Set (Regular q)) (a b : ℝ) :
    S ∩ trajectory q v x.val '' Icc a b = trajectory q v x.val '' visits q v x S a b := by
  ext y
  constructor
  · rintro ⟨hy, t, ht, rfl⟩
    exact ⟨t, ⟨hy, ht⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht.1, t, ht.2, rfl⟩

theorem intersection_count_eq (hmin : NativeDynamics.MinimalDirection q v) (x : CompleteOrbits q v)
    (S : Set (Regular q)) (a b : ℝ) :
    (S ∩ trajectory q v x.val '' Icc a b).ncard = (visits q v x S a b).ncard := by
  rw [intersection_eq_image]
  exact (trajectory_injective q v hmin x).injOn.ncard_image

theorem opposite_rates_eq {I : Type*} {l : Filter I} [NeBot l]
    (hmin : NativeDynamics.MinimalDirection q v) (x y : CompleteOrbits q v) (S : Set (Regular q))
    {T : I → ℝ} (hT : Tendsto T l atTop)
    (hgeom : ∀ᶠ n in l,
      (trajectory q v x.val '' Icc 0 (T n) ∩ S).ncard ≤ (trajectory q v y.val '' Icc (-(T n)) 0 ∩ S).ncard + 1 ∧
      (trajectory q v y.val '' Icc (-(T n)) 0 ∩ S).ncard ≤ (trajectory q v x.val '' Icc 0 (T n) ∩ S).ncard + 1)
    {a b : ℝ}
    (hx : Tendsto (fun n => ((visits q v x S 0 (T n)).ncard : ℝ) / T n) l (𝓝 a))
    (hy : Tendsto (fun n => ((visits q v y S (-(T n)) 0).ncard : ℝ) / T n) l (𝓝 b)) : a = b := by
  have hbounds : ∀ᶠ n in l,
      (visits q v x S 0 (T n)).ncard ≤ (visits q v y S (-(T n)) 0).ncard + 1 ∧
      (visits q v y S (-(T n)) 0).ncard ≤ (visits q v x S 0 (T n)).ncard + 1 := by
    filter_upwards [hgeom] with n hn
    rw [inter_comm (trajectory q v x.val '' Icc 0 (T n)) S,
      inter_comm (trajectory q v y.val '' Icc (-(T n)) 0) S,
      intersection_count_eq q v hmin x S 0 (T n), intersection_count_eq q v hmin y S (-(T n)) 0] at hn
    exact hn
  exact BoundedCountRates.limits_eq 1 hT hbounds hx hy

end VeechDichotomy.NativeMinimalOrbitVisits
