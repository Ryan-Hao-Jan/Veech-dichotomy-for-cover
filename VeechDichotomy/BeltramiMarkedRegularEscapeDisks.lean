module

public import VeechDichotomy.BeltramiMarkedPrimitiveDisks
public import Mathlib.Order.Interval.Set.Infinite

/-! Actual escape disks whose LIMIT frontier is entirely regular.
A finite set is avoided by choosing a coordinate radius outside its
finite set of coordinate distances. Compact inverse disks control the
frontier, and actual native primitives give uniform nearby-fiber escape. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRegularEscapeDisks

open Set Filter Topology

section ChartDisks

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]

def chartDisk (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) (r : ℝ) : Set Ω :=
  c.source ∩ c ⁻¹' Metric.ball z₀ r

omit [T2Space Ω] in
theorem chartDisk_open (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) (r : ℝ) : IsOpen (chartDisk c z₀ r) :=
  c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball

theorem frontier_coordinates (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) (r : ℝ)
    (hR : Metric.closedBall z₀ r ⊆ c.target) {y : Ω} (hy : y ∈ frontier (chartDisk c z₀ r)) :
    y ∈ c.source ∧ dist (c y) z₀ = r := by
  have hcompact : IsCompact (c.symm '' Metric.closedBall z₀ r) :=
    (isCompact_closedBall z₀ r).image_of_continuousOn (c.symm.continuousOn.mono hR)
  have hsub : chartDisk c z₀ r ⊆ c.symm '' Metric.closedBall z₀ r := by
    intro x hx
    exact ⟨c x, Metric.ball_subset_closedBall hx.2, c.left_inv hx.1⟩
  have hclosure : closure (chartDisk c z₀ r) ⊆ c.symm '' Metric.closedBall z₀ r :=
    closure_minimal hsub hcompact.isClosed
  obtain ⟨z, hz, rfl⟩ := hclosure hy.1
  have htarget := hR hz
  have hsource := c.map_target htarget
  have hcoord := c.right_inv htarget
  have hU : IsOpen (chartDisk c z₀ r) := chartDisk_open c z₀ r
  have hnot : c.symm z ∉ chartDisk c z₀ r := by
    intro hx
    apply hy.2
    rw [hU.interior_eq]
    exact hx
  have hnball : z ∉ Metric.ball z₀ r := by
    intro hzb
    exact hnot ⟨hsource, by simpa only [mem_preimage, hcoord] using hzb⟩
  refine ⟨hsource, ?_⟩
  rw [hcoord]
  exact le_antisymm hz (le_of_not_gt hnball)

theorem radius_avoiding_finite (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (htarget : Metric.closedBall z₀ R ⊆ c.target) {S : Set Ω} (hS : S.Finite) :
    ∃ r ∈ Ioo (R / 2) R, ∀ y ∈ frontier (chartDisk c z₀ r), y ∉ S := by
  let D := (fun y : Ω => dist (c y) z₀) '' (S ∩ c.source)
  have hD : D.Finite := (hS.inter_of_left c.source).image _
  obtain ⟨r, hr, hrD⟩ := (Ioo_infinite (show R / 2 < R by linarith)).exists_notMem_finite hD
  refine ⟨r, hr, ?_⟩
  intro y hy hyS
  have hsmall : Metric.closedBall z₀ r ⊆ c.target :=
    fun _ hz => htarget (hz.trans hr.2.le)
  have hc := frontier_coordinates c z₀ r hsmall hy
  exact hrD ⟨y, ⟨hyS, hc.1⟩, hc.2⟩

end ChartDisks

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover BeltramiPlane NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem exists_regular_disk (p₀ : Base A) (y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) :
    ∃ j : X, ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.closedBall (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r,
        (p₀, z) ∈ BeltramiMarkedUniformPrimitiveBounds.domain π F hBranch (p₀.2, y₀.point) j) ∧
      ∀ y ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch (p₀.2, y₀.point) p₀
        (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r),
        y ∈ regularSet (fiberForm π F hBranch p₀) := by
  obtain ⟨j, R, hR, hsub⟩ := BeltramiMarkedPrimitiveDisks.exists_disk π F hBranch p₀ y₀
  let c := BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀
  have htarget : Metric.closedBall (c y₀) R ⊆ c.target := fun z hz => (hsub z hz).1
  obtain ⟨r, hr, hsafe⟩ := radius_avoiding_finite c (c y₀) hR htarget (zeroSet_finite (fiberForm π F hBranch p₀))
  refine ⟨j, r, by linarith [hr.1], ?_, ?_⟩
  · intro z hz
    exact hsub z (hz.trans hr.2.le)
  · intro y hy
    exact hsafe y hy

theorem uniform_regular_escape (p₀ : Base A) (y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧ ∃ U : Set (Base A), IsOpen U ∧ p₀ ∈ U ∧
      (∀ y ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch (p₀.2, y₀.point) p₀
        (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r),
        y ∈ regularSet (fiberForm π F hBranch p₀)) ∧
      (∀ p ∈ U, Metric.closedBall (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r ⊆
        (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p).target) ∧
      (∀ p ∈ U, ∀ x : CompleteOrbits (fiberForm π F hBranch p) vertical,
        x.val.val ∈ BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch (p₀.2, y₀.point) p
          (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r →
        ∃ τ ∈ Icc 0 (2 * M + 1), (trajectory (fiberForm π F hBranch p) vertical x.val τ).val ∈
          frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch (p₀.2, y₀.point) p
            (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r)) := by
  obtain ⟨j, r, hr, hsub, hsafe⟩ := exists_regular_disk π F hBranch p₀ y₀
  obtain ⟨M, hM, U, hU, hpU, hescape⟩ := BeltramiMarkedUniformPrimitiveEscape.uniform_escape π F hBranch
    (p₀.2, y₀.point) j p₀ _ r hsub
  obtain ⟨V, hV, hpV, htarget⟩ := BeltramiMarkedUniformSlices.compact_persistence π F hBranch
    (p₀.2, y₀.point) p₀ (isCompact_closedBall _ r) (fun z hz => (hsub z hz).1)
  exact ⟨r, hr, M, hM, U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, hsafe,
    fun p hp => htarget p hp.2, fun p hp => hescape p hp.1⟩

end VeechDichotomy.BeltramiMarkedRegularEscapeDisks
