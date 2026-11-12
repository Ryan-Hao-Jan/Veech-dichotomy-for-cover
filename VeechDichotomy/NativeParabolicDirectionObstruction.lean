module

public import VeechDichotomy.NativeShearZeroObstruction
public import VeechDichotomy.NativeDeformationAffine
public import VeechDichotomy.NativeTeichmullerRay

/-! In every nonzero native direction with a dense complete orbit, the
actual derivative group excludes every nontrivial unipotent fixing that
direction. The exact rotation used by the native Teichmuller ray is
used here as well, through genuine deformation and flow conjugacies. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeParabolicDirectionObstruction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeVeech NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences
open NativeShearMatrices NativePrimitiveRectangles Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

theorem not_mem_of_zero (b : X) (hb : b ∈ zeroSet q) (A : SL2) (v : Plane)
    {c : ℝ} (hc : c ≠ 0) (hAv : planeEquiv A v = c • vertical)
    (x : CompleteOrbits q v) (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val))
    {a : ℝ} (ha : a ≠ 0) : A⁻¹ * lower a * A ∉ derivativeGroup q := by
  rintro ⟨φ⟩
  have heq : A * (A⁻¹ * lower a * A) * A⁻¹ = lower a := by group
  let ψ := NativeAffinePowers.cast (transformed q A) heq (NativeDeformationAffine.conjugate q A φ)
  have hdeformed := (NativeDeformationFlow.orbit_dense_iff q A v x).mp hdense
  have hex : ∃ y : CompleteOrbits (transformed q A) (c • vertical),
      DenseRange (fun t : ℝ => (flow (transformed q A) (c • vertical) t y).val.val) := by
    apply Eq.mp (congrArg (fun w : Plane => ∃ y : CompleteOrbits (transformed q A) w,
      DenseRange (fun t : ℝ => (flow (transformed q A) w t y).val.val)) hAv)
    exact
      (show ∃ y : CompleteOrbits (transformed q A) (planeEquiv A v),
        DenseRange (fun t : ℝ => (flow (transformed q A) (planeEquiv A v) t y).val.val) from
        ⟨NativeDeformationFlow.completeHomeomorph q A v x, hdeformed⟩)
  obtain ⟨y, hy⟩ := hex
  let z := NativeDirectionRescaling.phaseHomeomorph (transformed q A) c hc vertical y
  have hz : DenseRange (fun t : ℝ => (flow (transformed q A) vertical t z).val.val) := by
    change Dense (range _) at hy ⊢
    rw [NativeDirectionRescaling.orbit_range (transformed q A) c hc vertical y] at hy
    exact hy
  have hbnew : (toOriginal q A).symm b ∈ zeroSet (transformed q A) := by
    rw [WholeDeformedDifferential.zeroSet_form]
    exact hb
  exact NativeShearZeroObstruction.not_dense_of_zero (transformed q A) ha ψ
    ((toOriginal q A).symm b) hbnew z hz

theorem rotated_shear_not_mem (hgenus : 2 ≤ genus X) (v : Plane) (hv : v ≠ 0)
    (x : CompleteOrbits q v) (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val))
    {a : ℝ} (ha : a ≠ 0) :
    (NativeTeichmullerRay.rotationToVertical v hv)⁻¹ * lower a *
      NativeTeichmullerRay.rotationToVertical v hv ∉ derivativeGroup q := by
  obtain ⟨b, hb⟩ := NativeGenusZeros.zeroSet_nonempty q hgenus
  have hAv : planeEquiv (NativeTeichmullerRay.rotationToVertical v hv) v =
      NativeTeichmullerRay.radius v • vertical := by
    rw [NativeTeichmullerRay.rotation_velocity]
    ext <;> simp [vertical]
  exact not_mem_of_zero q b hb _ v (NativeTeichmullerRay.radius_pos hv).ne' hAv x hdense ha

end VeechDichotomy.NativeParabolicDirectionObstruction
