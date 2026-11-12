module

public import VeechDichotomy.NativeAnalyticMarkTransport
public import VeechDichotomy.NativePuncturedFundamentalGroup
public import Mathlib.Topology.Sequences

/-! Convergent actual marked configurations eventually lie in one of the
constructed analytic transport neighborhoods. Their actual complex
displacements tend to zero. Compact distinct-configuration sets therefore
yield such a parametrized subsequence without an extra chart assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ConvergentConfigurationParameters

open MNEC.NativeAbelianDifferential NativeAnalyticMarkTransport ComplexDisplacementParameters
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] {m : ℕ}

theorem tuple_zero {b : Fin m → X} (A : Data b) : (A.tuple (zero m)).val = b := by
  funext i
  change (A.disks i).chart.symm 0 = b i
  rw [← A.centers i, ← (A.disks i).chart_center]
  exact (A.disks i).chart.left_inv (A.disks i).center_source

theorem eventually_parameters {b : Fin m → X} (A : Data b) (u : ℕ → Fin m → X)
    (hu : Tendsto u atTop (𝓝 b)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → Parameters m,
      Tendsto a atTop (𝓝 (zero m)) ∧ ∀ n, (A.tuple (a n)).val = u (σ n) := by
  have hmem : ∀ᶠ n in atTop, u n ∈ A.marks.neighborhood :=
    hu (A.marks.open_neighborhood.mem_nhds A.marks.contains)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmem
  let σ : ℕ → ℕ := fun n => n + N
  have hσ : StrictMono σ := fun _ _ h => Nat.add_lt_add_right h N
  let v (n : ℕ) : A.marks.neighborhood := ⟨u (σ n), hN (σ n) (Nat.le_add_left N n)⟩
  have hv : Tendsto v atTop (𝓝 (⟨b, A.marks.contains⟩ : A.marks.neighborhood)) :=
    tendsto_subtype_rng.mpr (hu.comp hσ.tendsto_atTop)
  let a : ℕ → Parameters m := fun n => configurationHomeomorph A.disks (v n)
  have hzero : configurationHomeomorph A.disks (⟨b, A.marks.contains⟩ : A.marks.neighborhood) = zero m := by
    apply Subtype.ext
    funext i
    change (A.disks i).chart (b i) = 0
    rw [← A.centers i, (A.disks i).chart_center]
  have ha : Tendsto a atTop (𝓝 (zero m)) := by
    have h := (configurationHomeomorph A.disks).continuous.continuousAt.tendsto.comp hv
    rwa [hzero] at h
  refine ⟨σ, hσ, a, ha, ?_⟩
  intro n
  have htuple : A.tuple (a n) = v n := (configurationHomeomorph A.disks).symm_apply_apply (v n)
  exact congrArg Subtype.val htuple

variable [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem compact_configuration_subsequence (q : Differential X) (u : ℕ → Fin m → X)
    {F : Set (Fin m → X)} (hF : IsCompact F) (hu : ∀ n, u n ∈ F) (hconf : F ⊆ configuration m X) :
    ∃ b ∈ F, ∃ A : Data b, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → Parameters m,
      Tendsto a atTop (𝓝 (zero m)) ∧ ∀ n, (A.tuple (a n)).val = u (σ n) := by
  let : SecondCountableTopology X := ChartedSpace.secondCountable_of_sigmaCompact ℂ X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨b, hb, τ, hτ, hconv⟩ := hF.tendsto_subseq hu
  let A := chosenData q b (hconf hb)
  obtain ⟨υ, hυ, a, ha, htuple⟩ := eventually_parameters A (u ∘ τ) hconv
  exact ⟨b, hb, A, τ ∘ υ, hτ.comp hυ, a, ha, htuple⟩

end VeechDichotomy.ConvergentConfigurationParameters
