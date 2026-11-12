module

public import VeechDichotomy.BeltramiMarkedRectangleChains
public import VeechDichotomy.BeltramiMarkedRectangleLocalMeans
public import VeechDichotomy.BeltramiMarkedSimultaneousProfilePoints

/-! Global comparison of native source statistical means with regular
translated image limits. Actual persistent family rectangles connect
the regular limit fiber. Fixed conull-source anchors in their overlaps
are selected on ONE common subsequence, preserving all source profiles.
The proved unrestricted local comparison propagates along that finite chain. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedGlobalRegularMeans

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiMarkedLimitRectangles
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
    (x₀ y₀ : Regular (fiberForm π F hBranch p₀))
    (x y : CompleteOrbits q vertical) (dx dy : ℕ → ℝ) {dx₀ dy₀ : ℝ}
    (hdx : Tendsto dx atTop (𝓝 dx₀)) (hdy : Tendsto dy atTop (𝓝 dy₀))
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (P x dx n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀.val)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (P y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀.val)))
    (ht : Tendsto t atTop atTop) {mx my : ℝ}
    (hpx : NativeFlowboxProfileSets.FullProfile q D R x mx)
    (hpy : NativeFlowboxProfileSets.FullProfile q D R y my) : mx = my := by
  classical
  obtain ⟨B, hxB⟩ := covers_regular π F hBranch p₀ hzero x₀
  obtain ⟨C, hyC⟩ := covers_regular π F hBranch p₀ hzero y₀
  obtain ⟨n, f, hf0, hfn, hstep⟩ := BeltramiMarkedRectangleChains.finite_chain π F hBranch p₀ hzero B C
  have hxF : x₀.val ∈ (f 0).region := hf0.symm ▸ hxB
  have hyF : y₀.val ∈ (f n).region := hfn.symm ▸ hyC
  cases n with
  | zero =>
    exact BeltramiMarkedRectangleLocalMeans.mean_eq π F hBranch q hv t p e D hmin p₀ hp hzero E hE hEP
      (f 0) x₀.val y₀.val hxF hyF x y dx dy hdx hdy hx hy ht hpx hpy
  | succ n =>
    have hex : ∀ i : Fin (n + 1), ∃ w : Regular (fiberForm π F hBranch p₀),
        w ∈ (f i.val).regularRegion ∧ w ∈ (f (i.val + 1)).regularRegion := by
      intro i
      exact hstep i.val i.isLt
    choose w hw using hex
    let W : Fin (n + 1) → Set (Total π F hBranch) :=
      fun i => (f i.val).totalRegion ∩ (f (i.val + 1)).totalRegion
    have hW : ∀ i, IsOpen (W i) := fun i => (f i.val).totalRegion_open.inter (f (i.val + 1)).totalRegion_open
    have hwW : ∀ i, inclusion π F hBranch p₀ (w i).val ∈ W i := fun i => hw i
    obtain ⟨σ, hσ, hsim⟩ := BeltramiMarkedSimultaneousProfilePoints.common_subsequence π F hBranch q vertical hv t p e
      (fun z => ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D R z mz) E hE hEP p₀ hp hzero
      (fun i => (w i).val) (fun i => (w i).property) W hW hwW
    have hanchor : ∀ i : Fin (n + 1), ∃ (z : CompleteOrbits q vertical) (mz : ℝ)
        (u : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2),
        NativeFlowboxProfileSets.FullProfile q D R z mz ∧ inclusion π F hBranch p₀ u ∈ W i ∧
        Tendsto (fun k => inclusion π F hBranch (p (σ k))
          (BeltramiMarkedRayOrbitCounts.point π F hBranch q vertical hv t p e z.val (σ k)).val)
          atTop (𝓝 (inclusion π F hBranch p₀ u)) := by
      intro i
      obtain ⟨z, ⟨mz, hzp⟩, u, _, huW, hlim⟩ := hsim i
      exact ⟨z, mz, u, hzp, huW, hlim⟩
    choose z mz u hpz huW hlimz using hanchor
    have hclock : Tendsto R atTop atTop := NativeRayReferenceTimes.reference_tendsto vertical hv ht
    let Rσ := R ∘ σ
    have hEPσ : ∀ a ∈ E, ∃ z : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical z = a ∧
        ∃ mz : ℝ, NativeFlowboxProfileSets.FullProfile q D Rσ z mz := by
      intro a ha
      obtain ⟨z, hza, mz, hzp⟩ := hEP a ha
      exact ⟨z, hza, mz, NativeFlowboxProfileSets.subsequence q D R hclock z mz hzp σ hσ⟩
    have hpxσ := NativeFlowboxProfileSets.subsequence q D R hclock x mx hpx σ hσ
    have hpyσ := NativeFlowboxProfileSets.subsequence q D R hclock y my hpy σ hσ
    have hpzσ (i : Fin (n + 1)) := NativeFlowboxProfileSets.subsequence q D R hclock (z i) (mz i) (hpz i) σ hσ
    have hxσ : Tendsto (fun k => inclusion π F hBranch (p (σ k))
        (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun j => e (σ j)) x (dx ∘ σ) k).val)
        atTop (𝓝 (inclusion π F hBranch p₀ x₀.val)) := by
      simp_rw [BeltramiMarkedNativePointValues.shifted_point_subsequence]
      exact hx.comp hσ.tendsto_atTop
    have hyσ : Tendsto (fun k => inclusion π F hBranch (p (σ k))
        (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun j => e (σ j)) y (dy ∘ σ) k).val)
        atTop (𝓝 (inclusion π F hBranch p₀ y₀.val)) := by
      simp_rw [BeltramiMarkedNativePointValues.shifted_point_subsequence]
      exact hy.comp hσ.tendsto_atTop
    have hzσ (i : Fin (n + 1)) : Tendsto (fun k => inclusion π F hBranch (p (σ k))
        (point π F hBranch q vertical hv (t ∘ σ) (p ∘ σ) (fun j => e (σ j)) (z i) (fun _ => 0) k).val)
        atTop (𝓝 (inclusion π F hBranch p₀ (u i))) := by
      simp_rw [BeltramiMarkedNativePointValues.point_zero_shift, BeltramiMarkedNativePointValues.point_subsequence]
      exact hlimz i
    have localCompare := BeltramiMarkedRectangleLocalMeans.mean_eq π F hBranch q hv (t ∘ σ) (p ∘ σ)
      (fun j => e (σ j)) D hmin p₀ (hp.comp hσ.tendsto_atTop) hzero E hE hEPσ
    have hzeroTime : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hvalues : ∀ k (hk : k < n + 1), mx = mz ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact localCompare (f 0) x₀.val (u ⟨0, hk⟩) hxF (huW ⟨0, hk⟩).1
          x (z ⟨0, hk⟩) (dx ∘ σ) (fun _ => 0) (hdx.comp hσ.tendsto_atTop) hzeroTime
          hxσ (hzσ ⟨0, hk⟩) (ht.comp hσ.tendsto_atTop) hpxσ (hpzσ ⟨0, hk⟩)
      | succ k ih =>
        intro hk
        have hprev : k < n + 1 := by omega
        have heq : mz ⟨k, hprev⟩ = mz ⟨k + 1, hk⟩ :=
          localCompare (f (k + 1)) (u ⟨k, hprev⟩) (u ⟨k + 1, hk⟩) (huW ⟨k, hprev⟩).2 (huW ⟨k + 1, hk⟩).1
            (z ⟨k, hprev⟩) (z ⟨k + 1, hk⟩) (fun _ => 0) (fun _ => 0) hzeroTime hzeroTime
            (hzσ ⟨k, hprev⟩) (hzσ ⟨k + 1, hk⟩) (ht.comp hσ.tendsto_atTop) (hpzσ ⟨k, hprev⟩) (hpzσ ⟨k + 1, hk⟩)
        exact (ih hprev).trans heq
    have hlast : mz ⟨n, Nat.lt_succ_self n⟩ = my :=
      localCompare (f (n + 1)) (u ⟨n, Nat.lt_succ_self n⟩) y₀.val (huW ⟨n, Nat.lt_succ_self n⟩).2 hyF
        (z ⟨n, Nat.lt_succ_self n⟩) y (fun _ => 0) (dy ∘ σ) hzeroTime (hdy.comp hσ.tendsto_atTop)
        (hzσ ⟨n, Nat.lt_succ_self n⟩) hyσ (ht.comp hσ.tendsto_atTop) (hpzσ ⟨n, Nat.lt_succ_self n⟩) hpyσ
    exact (hvalues n (Nat.lt_succ_self n)).trans hlast

end VeechDichotomy.BeltramiMarkedGlobalRegularMeans
