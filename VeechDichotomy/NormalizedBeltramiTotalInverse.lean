module

public import VeechDichotomy.UniformBeltramiDisks
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The normalized fiber inverses come from one actual total-family
holomorphic chart inverse. Thus the varying complex parameter is part of
the analytic map, including at the marked section and differential zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedBeltramiTotalInverse

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiDiskData UniformBeltramiDisks BeltramiChartNormalization
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def input (r : ℝ) (p : ℂ × ℂ) : ℂ × ℂ := (p.1, (scale r)⁻¹ * p.2)

theorem input_contDiff (r : ℝ) : ContDiff ℂ ω (input r) :=
  contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : X} {μ₀ : Parameter} {U : Set X} (D : Data q b μ₀ U)

def inverse (p : ℂ × ℂ) : NativeBeltramiTotalSpace.TotalSpace q :=
  (NativeBeltramiTotalSpace.chart q ⟨(μ₀, b)⟩).symm (input D.radius p)

theorem holomorphicAt {p : ℂ × ℂ}
    (hp : input D.radius p ∈ (NativeBeltramiCharts.chart q b).target) :
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (inverse D) p := by
  have hInv : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (NativeBeltramiTotalSpace.chart q ⟨(μ₀, b)⟩).symm (input D.radius p) :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, b)⟩ : NativeBeltramiTotalSpace.TotalSpace q)) hp
  exact hInv.comp p ((input_contDiff D.radius).contMDiff p)

theorem uniform_holomorphicAt (μ : Near D) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (inverse D) (μ.val.val, z) :=
  holomorphicAt D (D.raw_target μ.val μ.property _ (inverse_scale_bound D.radius_pos hz))

theorem inverse_value (μ : Near D) (z : ℂ) :
    inverse D (μ.val.val, z) =
      ⟨(μ.val, ((normalizedChart D μ).symm z).point)⟩ := by
  apply (NativeBeltramiTotalSpace.toProduct q).injective
  refine Prod.ext ?_ ?_
  · exact BeltramiParameter.chart.left_inv (mem_univ μ.val)
  · exact (normalized_inverse_value D μ z).symm

theorem inverse_parameter (μ : Near D) (z : ℂ) :
    NativeBeltramiTotalSpace.projection q (inverse D (μ.val.val, z)) = μ.val := by
  rw [inverse_value]
  rfl

end VeechDichotomy.NormalizedBeltramiTotalInverse
