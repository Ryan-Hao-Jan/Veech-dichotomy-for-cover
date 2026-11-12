module

public import VeechDichotomy.BeltramiMarkedShiftedFlowboxCounts

/-! The local mean comparison remains valid after bounded ray-time
translations of each complete source orbit. Statistical hypotheses are
used only at the ORIGINAL fixed source points. Thus regular translated
image limits suffice, even if the untranslated images approach zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedShiftedMeanEquality

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup
open BeltramiMarkedShiftedSourcePoints
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (hv : vertical ≠ (0 : Plane)) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q vertical hv (t n)) (fiberForm π F hBranch (p n)))
local notation "τ" => time π F hBranch q vertical hv t p e
local notation "P" => point π F hBranch q vertical hv t p e
local notation "R" => (fun n => NativeRayReferenceTimes.reference vertical (t n))

theorem horizontally_distinct (D : NativeBufferedFlowboxes.Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {l r bot top : ℝ}
    (hR : ∀ a ∈ Icc l r ×ˢ Icc bot top, toPlane.symm a ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hxR : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀) ∈ rectangle l r bot top)
    (hyR : coordinate π F hBranch s (inclusion π F hBranch p₀ y₀) ∈ rectangle l r bot top)
    (hhor : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1 ≠
      (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1)
    (x y : CompleteOrbits q vertical) (dx dy : ℕ → ℝ) {dx₀ dy₀ : ℝ}
    (hdx : Tendsto dx atTop (𝓝 dx₀)) (hdy : Tendsto dy atTop (𝓝 dy₀))
    (lo hi : ℝ) (hlo : bot < lo) (hhi : hi < top) (hlohi : lo < hi)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (P x dx n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (P y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀)))
    (ht : Tendsto t atTop atTop) {mx my : ℝ}
    (hpx : NativeFlowboxProfileSets.CrossingProfile q D R x mx)
    (hpy : NativeFlowboxProfileSets.CrossingProfile q D R y my) : mx = my := by
  have hxlo := time_ratio_tendsto π F hBranch q vertical hv t p e s p₀ x₀ hx₀ x dx hdx lo hx
  have hxhi := time_ratio_tendsto π F hBranch q vertical hv t p e s p₀ x₀ hx₀ x dx hdx hi hx
  have hylo := time_ratio_tendsto π F hBranch q vertical hv t p e s p₀ y₀ hy₀ y dy hdy lo hy
  have hyhi := time_ratio_tendsto π F hBranch q vertical hv t p e s p₀ y₀ hy₀ y dy hdy hi hy
  have hmx := hpx (τ s x dx lo) (τ s x dx hi) _ _ hxlo hxhi (by linarith)
  have hmy := hpy (τ s y dy lo) (τ s y dy hi) _ _ hylo hyhi (by linarith)
  simp_rw [interval_length] at hmx hmy
  have hlength := BeltramiMarkedShiftedClocks.length_tendsto vertical hv t ht hlohi
  have hcounts : ∀ᶠ n in atTop,
      SeparatedWindowCounts.count (D.closedHits x) (τ s x dx lo n) (τ s x dx hi n) ≤
        SeparatedWindowCounts.count (D.closedHits y) (τ s y dy lo n) (τ s y dy hi n) + 1 ∧
      SeparatedWindowCounts.count (D.closedHits y) (τ s y dy lo n) (τ s y dy hi n) ≤
        SeparatedWindowCounts.count (D.closedHits x) (τ s x dx lo n) (τ s x dx hi n) + 1 := by
    rcases lt_or_gt_of_ne hhor with hxy | hyx
    · exact BeltramiMarkedShiftedFlowboxCounts.comparison π F hBranch q hv t p e D hmin s hs hreg p₀
        x₀ y₀ hx₀ hy₀ hR hxR hyR hxy x y dx dy lo hi hlo hhi hx hy
    · have hbnd := BeltramiMarkedShiftedFlowboxCounts.comparison π F hBranch q hv t p e D hmin s hs hreg p₀
        y₀ x₀ hy₀ hx₀ hR hyR hxR hyx y x dy dx lo hi hlo hhi hy hx
      filter_upwards [hbnd] with n hn
      exact ⟨hn.2, hn.1⟩
  have heq := BoundedCountRates.limits_eq 1 hlength hcounts hmx hmy
  exact (div_left_inj' D.height_pos.ne').mp heq

end VeechDichotomy.BeltramiMarkedShiftedMeanEquality
