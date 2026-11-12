module

public import VeechDichotomy.HolomorphicCotangentCoefficients
public import VeechDichotomy.NativeAnalyticCoverForm

/-! Joint holomorphicity and continuity of the actual family differential
coefficients in local tangent frames, including the vertical direction.
The continuity uses the original parameter/source product topology and
does not impose a fixed zero divisor or a stratum restriction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverCoefficients

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open NativeAnalyticCoverTotalSpace ComplexDisplacementParameters NativeAnalyticCoverForm
open HolomorphicCotangentCoefficients Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π)

def verticalCoefficient (center : TotalSpace π A hBranch) : TotalSpace π A hBranch → ℂ :=
  coefficient (form π A hBranch) center (0, 1)

theorem coefficient_holomorphic (center : TotalSpace π A hBranch) (v : Space m × ℂ) :
    ContMDiffOn 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) ω (coefficient (form π A hBranch) center v)
      (chart π A hBranch center).source := by
  simpa only [frame, TangentBundle.trivializationAt_baseSet] using!
    HolomorphicCotangentCoefficients.coefficient_holomorphic (form π A hBranch) center v

theorem verticalCoefficient_holomorphic (center : TotalSpace π A hBranch) :
    ContMDiffOn 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) ω (verticalCoefficient π A hBranch center)
      (chart π A hBranch center).source := coefficient_holomorphic π A hBranch center (0, 1)

theorem verticalCoefficient_continuousAt (center : TotalSpace π A hBranch) {p : TotalSpace π A hBranch}
    (hp : p ∈ (chart π A hBranch center).source) : ContinuousAt (verticalCoefficient π A hBranch center) p :=
  ((verticalCoefficient_holomorphic π A hBranch center).contMDiffAt
    ((chart π A hBranch center).open_source.mem_nhds hp)).continuousAt

theorem continuousOn_product (center : TotalSpace π A hBranch) :
    ContinuousOn (fun p : Parameters m × Y => verticalCoefficient π A hBranch center ((toProduct π A hBranch).symm p))
      ((toProduct π A hBranch).symm ⁻¹' (chart π A hBranch center).source) :=
  (verticalCoefficient_holomorphic π A hBranch center).continuousOn.comp
    (toProduct π A hBranch).symm.continuous.continuousOn (fun _ hp => hp)

theorem coefficient_tendsto {J : Type*} {l : Filter J} (center : TotalSpace π A hBranch)
    {p : TotalSpace π A hBranch} (hp : p ∈ (chart π A hBranch center).source)
    {f : J → TotalSpace π A hBranch} (hf : Tendsto f l (𝓝 p)) :
    Tendsto (fun j => verticalCoefficient π A hBranch center (f j)) l
      (𝓝 (verticalCoefficient π A hBranch center p)) :=
  (verticalCoefficient_continuousAt π A hBranch center hp).tendsto.comp hf

end VeechDichotomy.NativeAnalyticCoverCoefficients
