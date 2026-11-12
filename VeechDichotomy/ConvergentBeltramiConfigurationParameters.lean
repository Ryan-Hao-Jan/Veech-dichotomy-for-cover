module

public import VeechDichotomy.UniformBeltramiConfigurationCoordinates
public import VeechDichotomy.BeltramiMarkedReferenceCharts
public import Mathlib.Topology.Sequences

/-! Convergent actual base parameters and marked tuples eventually
have genuine uniform transport parameters converging to the reference
parameter. The constructed transports move the reference marks EXACTLY
to the given tuples, with no independent chart-choice assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ConvergentBeltramiConfigurationParameters

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

theorem coordinate_tendsto (μ : ℕ → Parameter) (u : ℕ → Fin m → X)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hu : Tendsto u atTop (𝓝 b)) (i : Fin m) :
    Tendsto (fun n => coordinate A i (μ n, u n)) atTop (𝓝 0) := by
  have hc := (coordinate_continuousAt A i (p := (μ₀, b)) (NativePowerCharts.chosen q (b i)).center).tendsto
  have h := hc.comp (hμ.prodMk_nhds hu)
  simpa only [Function.comp_def, coordinate_center] using! h

theorem eventually_valid (μ : ℕ → Parameter) (u : ℕ → Fin m → X)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hu : Tendsto u atTop (𝓝 b)) :
    ∀ᶠ n in atTop, Valid A (μ n) (u n) := by
  have hbase : ∀ᶠ n in atTop, μ n ∈ A.baseNeighborhood := hμ (A.baseNeighborhood_open.mem_nhds A.reference_mem)
  have hi (i : Fin m) : ∀ᶠ n in atTop,
      u n i ∈ (NativePowerCharts.chosen q (b i)).chart.source ∧ ‖coordinate A i (μ n, u n)‖ < 1 / 2 := by
    have hs : ∀ᶠ n in atTop, u n i ∈ (NativePowerCharts.chosen q (b i)).chart.source :=
      (((continuous_apply i).continuousAt.tendsto).comp hu)
        ((NativePowerCharts.chosen q (b i)).chart.open_source.mem_nhds (NativePowerCharts.chosen q (b i)).center)
    have hn : ∀ᶠ n in atTop, ‖coordinate A i (μ n, u n)‖ < 1 / 2 :=
      (coordinate_tendsto A μ u hμ hu i).norm (isOpen_Iio.mem_nhds (by norm_num))
    exact hs.and hn
  exact hbase.and (eventually_all.mpr hi)

theorem raw_tendsto (μ : ℕ → Parameter) (u : ℕ → Fin m → X)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hu : Tendsto u atTop (𝓝 b)) :
    Tendsto (fun n => ((μ n).val, fun i => coordinate A i (μ n, u n))) atTop
      (𝓝 (μ₀.val, (0 : Fin m → ℂ))) :=
  (continuous_subtype_val.continuousAt.tendsto.comp hμ).prodMk_nhds
    (tendsto_pi_nhds.mpr fun i => coordinate_tendsto A μ u hμ hu i)

theorem eventually_parameters (F : Family A) (μ : ℕ → Parameter) (u : ℕ → Fin m → X)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hu : Tendsto u atTop (𝓝 b)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ComplexBeltramiMarkParameters.Parameters A,
      Tendsto a atTop (𝓝 (ComplexBeltramiMarkParameters.reference A)) ∧
      ∀ n, BeltramiMarkedReferenceCharts.parameter A (a n) = μ (σ n) ∧ tuple A F (a n) = u (σ n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_valid A μ u hμ hu)
  let σ : ℕ → ℕ := fun n => n + N
  have hσ : StrictMono σ := fun _ _ h => Nat.add_lt_add_right h N
  let a : ℕ → ComplexBeltramiMarkParameters.Parameters A := fun n =>
    parameters A (μ (σ n)) (u (σ n)) (hN (σ n) (Nat.le_add_left N n))
  have ha : Tendsto a atTop (𝓝 (ComplexBeltramiMarkParameters.reference A)) :=
    tendsto_subtype_rng.mpr ((raw_tendsto A μ u hμ hu).comp hσ.tendsto_atTop)
  refine ⟨σ, hσ, a, ha, ?_⟩
  intro n
  refine ⟨?_, parameters_moves A F (μ (σ n)) (u (σ n)) (hN (σ n) (Nat.le_add_left N n))⟩
  apply Subtype.ext
  rfl

end VeechDichotomy.ConvergentBeltramiConfigurationParameters
