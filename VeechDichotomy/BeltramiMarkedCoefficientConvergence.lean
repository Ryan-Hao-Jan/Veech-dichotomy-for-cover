module

public import VeechDichotomy.BeltramiMarkedRelativeCoefficients
public import VeechDichotomy.CompactFiberTubes

/-! Genuine compact uniform convergence of the native relative
coefficients and every derivative in fixed total charts. The actual
joint analytic expressions proved previously discharge all continuity
inputs. Their common domains also persist on nearby fibers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedCoefficientConvergence

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedCoverCoordinates BeltramiMarkedRelativeCoefficients
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem uniform_coefficient (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {K : Set ℂ} (hK : IsCompact K)
    (hsub : ∀ z ∈ K, (a.val, z) ∈ domain π F hBranch s j) :
    TendstoUniformlyOn (fun u z => coefficient π F hBranch s j (u, z))
      (fun z => coefficient π F hBranch s j (a.val, z)) (𝓝 a.val) K :=
  CompactFiberTubes.tendstoUniformlyOn (domain_open π F hBranch s j)
    (BeltramiMarkedRelativeCoefficients.continuousOn π F hBranch s j) a.val hK hsub

theorem uniform_derivatives (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hsub : ∀ z ∈ K, (a.val, z) ∈ domain π F hBranch s j) :
    TendstoUniformlyOn (fun u z => iteratedFDeriv ℂ k (coefficient π F hBranch s j) (u, z))
      (fun z => iteratedFDeriv ℂ k (coefficient π F hBranch s j) (a.val, z)) (𝓝 a.val) K :=
  CompactFiberTubes.tendstoUniformlyOn (domain_open π F hBranch s j)
    (fun _ hp => (derivative_holomorphicAt π F hBranch s j k hp).continuousAt.continuousWithinAt) a.val hK hsub

theorem along_parameters {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {K : Set ℂ} (hK : IsCompact K)
    (hsub : ∀ z ∈ K, (a.val, z) ∈ domain π F hBranch s j)
    {f : I → ComplexBeltramiMarkParameters.Parameters A} (hf : Tendsto f l (𝓝 a)) :
    TendstoUniformlyOn (fun i z => coefficient π F hBranch s j ((f i).val, z))
      (fun z => coefficient π F hBranch s j (a.val, z)) l K := by
  have hval := continuous_subtype_val.continuousAt.tendsto.comp hf
  intro u hu
  exact hval (uniform_coefficient π F hBranch s j a hK hsub u hu)

theorem eventual_domain {I : Type*} {l : Filter I}
    (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X)
    (a : ComplexBeltramiMarkParameters.Parameters A) {K : Set ℂ} (hK : IsCompact K)
    (hsub : ∀ z ∈ K, (a.val, z) ∈ domain π F hBranch s j)
    {f : I → ComplexBeltramiMarkParameters.Parameters A} (hf : Tendsto f l (𝓝 a)) :
    ∀ᶠ i in l, ∀ z ∈ K, ((f i).val, z) ∈ domain π F hBranch s j := by
  obtain ⟨U, hU, haU, hUD⟩ := CompactFiberTubes.exists_open_tube (domain_open π F hBranch s j) a.val hK hsub
  have hval := continuous_subtype_val.continuousAt.tendsto.comp hf
  filter_upwards [hval (hU.mem_nhds haU)] with i hi
  exact hUD (f i).val hi

end VeechDichotomy.BeltramiMarkedCoefficientConvergence
