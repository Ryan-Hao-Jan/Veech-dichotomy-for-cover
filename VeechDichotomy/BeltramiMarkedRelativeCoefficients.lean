module

public import VeechDichotomy.BeltramiMarkedCoverCoordinates

/-! Actual relative pullback coefficient expressions in fixed total
charts. They and all their derivatives are jointly analytic on the
actual open covering-coordinate domain; zeros may merge or split. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRelativeCoefficients

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedCoverCoordinates
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def coefficient (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : ℂ :=
  ((NativePowerCharts.chosen qX j).exponent : ℂ) *
    expression π F hBranch s j p ^ ((NativePowerCharts.chosen qX j).exponent - 1) *
      verticalDerivative π F hBranch s j p

theorem holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hp : p ∈ domain π F hBranch s j) :
    ContDiffAt ℂ ω (coefficient π F hBranch s j) p :=
  (contDiffAt_const.mul ((expression_holomorphicAt π F hBranch s j hp).pow _)).mul
    (verticalDerivative_holomorphicAt π F hBranch s j hp)

theorem holomorphicOn (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) :
    ContDiffOn ℂ ω (coefficient π F hBranch s j) (domain π F hBranch s j) :=
  fun _ hp => (holomorphicAt π F hBranch s j hp).contDiffWithinAt

theorem continuousOn (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) :
    ContinuousOn (coefficient π F hBranch s j) (domain π F hBranch s j) := (holomorphicOn π F hBranch s j).continuousOn

theorem derivative_holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) (k : ℕ)
    {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hp : p ∈ domain π F hBranch s j) :
    ContDiffAt ℂ ω (iteratedFDeriv ℂ k (coefficient π F hBranch s j)) p :=
  (holomorphicAt π F hBranch s j hp).iteratedFDeriv_right (by simp)

theorem coefficient_tendsto {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    {p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hp : p ∈ domain π F hBranch s j)
    {f : I → ComplexBeltramiMarkParameters.Space (m := m) × ℂ} (hf : Tendsto f l (𝓝 p)) :
    Tendsto (fun i => coefficient π F hBranch s j (f i)) l (𝓝 (coefficient π F hBranch s j p)) :=
  (holomorphicAt π F hBranch s j hp).continuousAt.tendsto.comp hf

end VeechDichotomy.BeltramiMarkedRelativeCoefficients
