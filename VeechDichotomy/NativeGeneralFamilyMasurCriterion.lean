module

public import VeechDichotomy.NativeFamilyMasurCriterion
public import VeechDichotomy.NativeRayFactorization

/-! The actual native-family Masur criterion in EVERY nonzero original
direction. Rotate the entire actual source at time zero, factor its
genuine returning ray through the unit-vertical ray, and transport unique
ergodicity back by the proved native flow/measure equivalences. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeGeneralFamilyMasurCriterion

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane
open Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
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
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (A : SL2) : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance (A B : SL2) : ChartedSpace ℂ (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.chartedSpace (transformed q A) B
local instance (A B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface (transformed q A) B) :=
  WholeDeformedAtlas.isComplexManifold (transformed q A) B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

include π F hBranch hv e in
theorem uniquely_ergodic (hmin : NativeDynamics.MinimalDirection q v)
    (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (hzero : ∀ i, p₀.2.val.2 i = 0)
    (ht : Tendsto t atTop atTop) : NativeDynamics.UniquelyErgodicDirection q v := by
  let hV := NativeVerticalRayNormalization.vertical_ne_zero
  let qrot := NativeTeichmullerRay.rayForm q v hv 0
  have hminRot : NativeDynamics.MinimalDirection qrot vertical :=
    (NativeTeichmullerRay.minimal_vertical_iff q v hv 0).mp hmin
  let eRot := fun n => NativeDifferentialEquivalenceLaws.trans
    (NativeRayFactorization.equivalence q v hv hV (t n)) (e n)
  have hUE : NativeDynamics.UniquelyErgodicDirection qrot vertical :=
    NativeFamilyMasurCriterion.uniquely_ergodic π F hBranch qrot hV t p eRot hminRot p₀ hp hzero ht
  exact (NativeTeichmullerRay.uniquelyErgodic_vertical_iff q v hv 0).mpr hUE

end VeechDichotomy.NativeGeneralFamilyMasurCriterion
