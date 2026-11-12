module

public import VeechDichotomy.BeltramiMarkedTotalPrimitives
public import VeechDichotomy.BeltramiMarkedUniformSlices
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform bounds for the ACTUAL native fiber primitives in fixed
source-coordinate disks. Joint total continuity and compact fiber tubes
give one bound and one parameter neighborhood, including at zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedUniformPrimitiveBounds

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def domain (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) : Set (Base A × ℂ) :=
  BeltramiMarkedUniformSlices.domain π F hBranch s ∩
    BeltramiMarkedUniformSlices.inverse π F hBranch s ⁻¹' BeltramiMarkedTotalPrimitives.domain π F hBranch j

def value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) (t : Base A × ℂ) : ℂ :=
  BeltramiMarkedTotalPrimitives.primitive π F hBranch j (BeltramiMarkedUniformSlices.inverse π F hBranch s t)

theorem domain_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) : IsOpen (domain π F hBranch s j) :=
  (BeltramiMarkedUniformSlices.continuousOn_inverse π F hBranch s).isOpen_inter_preimage
    (BeltramiMarkedUniformSlices.domain_open π F hBranch s) (BeltramiMarkedTotalPrimitives.domain_open π F hBranch j)

theorem continuousOn_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) :
    ContinuousOn (value π F hBranch s j) (domain π F hBranch s j) :=
  (BeltramiMarkedTotalPrimitives.continuousOn_primitive π F hBranch j).comp
    ((BeltramiMarkedUniformSlices.continuousOn_inverse π F hBranch s).mono inter_subset_left) (fun _ ht => ht.2)

theorem value_inverse (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) (p : Base A) {z : ℂ}
    (hz : z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    value π F hBranch s j (p, z) = BeltramiMarkedPowerPrimitives.primitive π F hBranch j p
      ((BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z) := by
  rw [value, BeltramiMarkedUniformSlices.inverse_value π F hBranch s p hz,
    BeltramiMarkedTotalPrimitives.primitive_inclusion]

theorem uniform_bound (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) (p₀ : Base A)
    {K : Set ℂ} (hK : IsCompact K) (hsub : ∀ z ∈ K, (p₀, z) ∈ domain π F hBranch s j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ U : Set (Base A), IsOpen U ∧ p₀ ∈ U ∧
      ∀ p ∈ U, ∀ z ∈ K, z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target ∧
        (BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z ∈ BeltramiMarkedPowerPrimitives.domain π F hBranch j p ∧
        |(BeltramiMarkedPowerPrimitives.primitive π F hBranch j p ((BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z)).im| ≤ M := by
  have hcont : ContinuousOn (fun z => value π F hBranch s j (p₀, z)) K :=
    (continuousOn_value π F hBranch s j).comp (continuous_const.prodMk continuous_id).continuousOn hsub
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  let M := max C 0 + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hopen : IsOpen (domain π F hBranch s j ∩ value π F hBranch s j ⁻¹' Metric.ball (0 : ℂ) M) :=
    (continuousOn_value π F hBranch s j).isOpen_inter_preimage (domain_open π F hBranch s j) Metric.isOpen_ball
  have hstart : ∀ z ∈ K, (p₀, z) ∈ domain π F hBranch s j ∩ value π F hBranch s j ⁻¹' Metric.ball (0 : ℂ) M := by
    intro z hz
    refine ⟨hsub z hz, ?_⟩
    change dist (value π F hBranch s j (p₀, z)) 0 < M
    rw [dist_zero_right]
    exact (hC z hz).trans_lt (by dsimp [M]; linarith [le_max_left C 0])
  obtain ⟨U, hU, hpU, hUK⟩ := CompactFiberTubes.exists_open_tube hopen p₀ hK hstart
  refine ⟨M, hM, U, hU, hpU, ?_⟩
  intro p hp z hz
  have h := hUK p hp z hz
  have htarget : z ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target := h.1.1
  have hdomain : (BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z ∈
      BeltramiMarkedPowerPrimitives.domain π F hBranch j p := by
    apply (BeltramiMarkedTotalPrimitives.domain_inclusion π F hBranch j p _).mp
    rw [← BeltramiMarkedUniformSlices.inverse_value π F hBranch s p htarget]
    exact h.1.2
  have hnorm : ‖value π F hBranch s j (p, z)‖ ≤ M := by
    have hn : dist (value π F hBranch s j (p, z)) 0 < M := h.2
    simpa only [dist_zero_right] using hn.le
  rw [value_inverse π F hBranch s j p htarget] at hnorm
  exact ⟨htarget, hdomain, (Complex.abs_im_le_norm _).trans hnorm⟩

end VeechDichotomy.BeltramiMarkedUniformPrimitiveBounds
