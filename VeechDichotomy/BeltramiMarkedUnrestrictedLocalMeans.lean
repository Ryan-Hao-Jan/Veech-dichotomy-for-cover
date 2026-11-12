module

public import VeechDichotomy.BeltramiMarkedConullProfilePoints
public import VeechDichotomy.BeltramiMarkedShiftedMeanEquality

/-! Local source mean equality without ANY horizontal or vertical
ordering restriction on regular image limits. A fixed point from the
actual conull statistical source set is selected with a third regular
limit avoiding both horizontal coordinates; all profiles survive the
further subsequence and the two proved local comparisons finish. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedUnrestrictedLocalMeans

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
local instance : MeasurableSpace Z := borel Z
local instance : BorelSpace Z := ⟨rfl⟩

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q vertical hv (t n)) (fiberForm π F hBranch (p n)))
local notation "P" => point π F hBranch q vertical hv t p e
local notation "R" => (fun n => NativeRayReferenceTimes.reference vertical (t n))

theorem mean_eq (D : NativeBufferedFlowboxes.Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (E : Set Z) (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ w ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = w ∧
      ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D R z mz)
    (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {l r bot top : ℝ}
    (hR : ∀ a ∈ Icc l r ×ˢ Icc bot top, toPlane.symm a ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hxR : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀) ∈ rectangle l r bot top)
    (hyR : coordinate π F hBranch s (inclusion π F hBranch p₀ y₀) ∈ rectangle l r bot top)
    (x y : CompleteOrbits q vertical) (dx dy : ℕ → ℝ) {dx₀ dy₀ : ℝ}
    (hdx : Tendsto dx atTop (𝓝 dx₀)) (hdy : Tendsto dy atTop (𝓝 dy₀))
    (lo hi : ℝ) (hlo : bot < lo) (hhi : hi < top) (hlohi : lo < hi)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (P x dx n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (P y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀)))
    (ht : Tendsto t atTop atTop) {mx my : ℝ}
    (hpx : NativeFlowboxProfileSets.FullProfile q D R x mx)
    (hpy : NativeFlowboxProfileSets.FullProfile q D R y my) : mx = my := by
  let a := (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1
  let b := (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1
  obtain ⟨z, ⟨mz, hzp⟩, z₀, _, hzW, σ, hσ, hzlim⟩ := BeltramiMarkedConullProfilePoints.point_in_rectangle
    π F hBranch q vertical hv t p e (fun z => ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D R z mz)
    E hE hEP p₀ hp hzero s hs hreg (hxR.1.1.trans hxR.1.2) (hxR.2.1.trans hxR.2.2) hR a b
  have hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source := hzW.1
  have hzcoords : (coordinate π F hBranch s (inclusion π F hBranch p₀ z₀)).1 ∈ Ioo l r \ {a, b} ∧
      (coordinate π F hBranch s (inclusion π F hBranch p₀ z₀)).2 ∈ Ioo bot top := hzW.2
  have hzR : coordinate π F hBranch s (inclusion π F hBranch p₀ z₀) ∈ rectangle l r bot top :=
    ⟨hzcoords.1.1, hzcoords.2⟩
  have hxz : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1 ≠
      (coordinate π F hBranch s (inclusion π F hBranch p₀ z₀)).1 := by
    intro heq
    exact hzcoords.1.2 (Or.inl heq.symm)
  have hyz : (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1 ≠
      (coordinate π F hBranch s (inclusion π F hBranch p₀ z₀)).1 := by
    intro heq
    exact hzcoords.1.2 (Or.inr heq.symm)
  have hclock : Tendsto R atTop atTop := NativeRayReferenceTimes.reference_tendsto vertical hv ht
  have hxpσ := NativeFlowboxProfileSets.subsequence q D R hclock x mx hpx σ hσ
  have hypσ := NativeFlowboxProfileSets.subsequence q D R hclock y my hpy σ hσ
  have hzpσ := NativeFlowboxProfileSets.subsequence q D R hclock z mz hzp σ hσ
  have hxσ : Tendsto (fun n => inclusion π F hBranch (p (σ n))
      (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x (dx ∘ σ) n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ x₀)) := by
    simp_rw [BeltramiMarkedNativePointValues.shifted_point_subsequence]
    exact hx.comp hσ.tendsto_atTop
  have hyσ : Tendsto (fun n => inclusion π F hBranch (p (σ n))
      (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) y (dy ∘ σ) n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ y₀)) := by
    simp_rw [BeltramiMarkedNativePointValues.shifted_point_subsequence]
    exact hy.comp hσ.tendsto_atTop
  have hzσ : Tendsto (fun n => inclusion π F hBranch (p (σ n))
      (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) z (fun _ => 0) n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ z₀)) := by
    simp_rw [BeltramiMarkedNativePointValues.point_zero_shift, BeltramiMarkedNativePointValues.point_subsequence]
    exact hzlim
  have hxmean := BeltramiMarkedShiftedMeanEquality.horizontally_distinct π F hBranch q hv (t ∘ σ) (p ∘ σ)
    (fun k => e (σ k)) D hmin s hs hreg p₀ x₀ z₀ hx₀ hz₀ hR hxR hzR hxz x z (dx ∘ σ) (fun _ => 0)
    (hdx.comp hσ.tendsto_atTop) (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    lo hi hlo hhi hlohi hxσ hzσ (ht.comp hσ.tendsto_atTop) hxpσ.2.2 hzpσ.2.2
  have hymean := BeltramiMarkedShiftedMeanEquality.horizontally_distinct π F hBranch q hv (t ∘ σ) (p ∘ σ)
    (fun k => e (σ k)) D hmin s hs hreg p₀ y₀ z₀ hy₀ hz₀ hR hyR hzR hyz y z (dy ∘ σ) (fun _ => 0)
    (hdy.comp hσ.tendsto_atTop) (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    lo hi hlo hhi hlohi hyσ hzσ (ht.comp hσ.tendsto_atTop) hypσ.2.2 hzpσ.2.2
  exact hxmean.trans hymean.symm

end VeechDichotomy.BeltramiMarkedUnrestrictedLocalMeans
