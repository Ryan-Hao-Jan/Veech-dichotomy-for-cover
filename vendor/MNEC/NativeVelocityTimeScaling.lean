module

public import MNEC.NativeCompleteDirectionalFlow
public import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-! Actual maximal trajectories for scalar velocity changes on ANY native
holomorphic differential. Derived by native reparametrization and maximality. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeVelocityTimeScaling

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics
open NativeCompleteDirectionalFlow Set Topology
open scoped Manifold ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem field_smul (q : Differential X) (a : ℝ) (v : Plane) :
    letI := chartedSpace q
    field q (a • v) = a • field q v := by
  let := chartedSpace q
  funext x
  simp only [Pi.smul_apply, field_eq_const]

theorem scaled_curve_integral (q : Differential X) (a : ℝ) (v : Plane) (x : Regular q) :
    letI := chartedSpace q
    IsMIntegralCurveOn (fun t => trajectory q v x (t * a)) (field q (a • v))
      {t | t * a ∈ domain q v x} := by
  let := chartedSpace q
  rw [field_smul]
  exact (trajectory_isMIntegralCurveOn q v x).comp_mul a

theorem scaled_domain_subset (q : Differential X) (a : ℝ) (v : Plane) (x : Regular q) :
    {t | t * a ∈ domain q v x} ⊆ domain q (a • v) x ∧
      EqOn (trajectory q (a • v) x) (fun t => trajectory q v x (t * a))
        {t | t * a ∈ domain q v x} := by
  let := chartedSpace q
  apply extends_every_open_interval q (a • v) x
    {t | t * a ∈ domain q v x} (fun t => trajectory q v x (t * a))
  · exact (domain_open q v x).preimage (continuous_mul_const a)
  · have hconv := (domain_convex q v x).linear_preimage (LinearMap.lsmul ℝ ℝ a)
    have heq : (LinearMap.lsmul ℝ ℝ a) ⁻¹' domain q v x =
        {t | t * a ∈ domain q v x} := by
      ext t
      simp only [mem_preimage, LinearMap.lsmul_apply, smul_eq_mul, mul_comm a t, mem_ofPred_eq]
    rw [heq] at hconv
    exact hconv.ordConnected
  · simpa only [zero_mul, mem_ofPred_eq] using zero_mem_domain q v x
  · simpa only [zero_mul] using trajectory_initial q v x
  · exact scaled_curve_integral q a v x

theorem domain_smul (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) (x : Regular q) :
    domain q (a • v) x = {t | t * a ∈ domain q v x} := by
  apply Subset.antisymm
  · intro t ht
    have h := (scaled_domain_subset q a⁻¹ (a • v) x).1
    have hmem : t * a ∈ {s | s * a⁻¹ ∈ domain q (a • v) x} := by
      simpa only [mem_ofPred_eq, mul_assoc, mul_inv_cancel₀ ha, mul_one] using ht
    simpa only [inv_smul_smul₀ ha, mem_ofPred_eq] using h hmem
  · exact (scaled_domain_subset q a v x).1

theorem trajectory_smul (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) (x : Regular q)
    (t : ℝ) (ht : t ∈ domain q (a • v) x) :
    trajectory q (a • v) x t = trajectory q v x (t * a) := by
  apply (scaled_domain_subset q a v x).2
  rwa [domain_smul q a ha v x] at ht

theorem completeOrbitSet_smul (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) :
    completeOrbitSet q (a • v) = completeOrbitSet q v := by
  ext x
  change domain q (a • v) x = univ ↔ domain q v x = univ
  rw [domain_smul q a ha v x]
  constructor
  · intro h
    apply eq_univ_of_forall
    intro t
    have hm : t / a ∈ {s | s * a ∈ domain q v x} := by rw [h]; trivial
    simpa only [mem_ofPred_eq, div_mul_cancel₀ _ ha] using hm
  · intro h
    simp only [h, mem_univ, ofPred_true]

end MNEC.NativeVelocityTimeScaling

