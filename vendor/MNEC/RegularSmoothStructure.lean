module

public import MNEC.RegularTranslationStructure
public import MNEC.RegularTopologyArea
public import MNEC.RegularCountability
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

/-!
# The actual regular quotient as a standard smooth real manifold

Actual transition maps are locally translations. Such maps are `C^n` for
every regularity parameter, so the proved translation structure groupoid
embeds in mathlib's standard smooth groupoid. This constructs `IsManifold`
on the independently constructed native regular charted space. No smoothing,
directional flow, or vector-field hypothesis is assumed.

The imported topology interfaces provide the separately proved Hausdorff,
second-countable and locally compact structures on this same regular locus.
-/

noncomputable section

namespace MNEC.RegularSmoothStructure

open LatticeTorus SlitConnectedSum RegularChartedSpace TranslationGroupoid Set Topology
open scoped Manifold ContDiff

theorem contDiffAt_of_local_translation {f : Plane → Plane} {x : Plane} (n : ℕ∞ω)
    (h : ∃ v : Plane, ∀ᶠ y in 𝓝 x, f y = y + v) : ContDiffAt ℝ n f x := by
  obtain ⟨v, hv⟩ := h
  have htrans : ContDiff ℝ n (fun y : Plane => y + v) := contDiff_id.add contDiff_const
  exact htrans.contDiffAt.congr_of_eventuallyEq hv

theorem locallyTranslation_contDiffOn {f : Plane → Plane} {u : Set Plane} (n : ℕ∞ω)
    (hf : LocallyTranslationOn f u) : ContDiffOn ℝ n f u :=
  fun x hx => (contDiffAt_of_local_translation n (hf x hx)).contDiffWithinAt

theorem translationGroupoid_le_contDiffGroupoid (n : ℕ∞ω) :
    TranslationGroupoid.groupoid ≤ contDiffGroupoid n 𝓘(ℝ, Plane) := by
  apply StructureGroupoid.le_iff.2
  intro e he
  have htrans := (TranslationGroupoid.mem_groupoid_iff e).mp he
  change e ∈ (contDiffPregroupoid n 𝓘(ℝ, Plane)).groupoid
  rw [mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      (locallyTranslation_contDiffOn n htrans.1 : ContDiffOn ℝ n e e.source)
  · simpa only [contDiffPregroupoid, mfld_simps] using
      (locallyTranslation_contDiffOn n htrans.2 : ContDiffOn ℝ n e.symm e.target)

/-- Standard mathlib real manifold structure on the actual regular locus,
for every `n`, deduced from the actual translation transitions. -/
theorem isManifold {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (n : ℕ∞ω) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    IsManifold 𝓘(ℝ, Plane) n (Regular L₁ L₂ w) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  let : HasGroupoid (Regular L₁ L₂ w) TranslationGroupoid.groupoid :=
    RegularTranslationStructure.has_translation_groupoid hw₁ hw₂
  let : HasGroupoid (Regular L₁ L₂ w) (contDiffGroupoid n 𝓘(ℝ, Plane)) :=
    hasGroupoid_of_le (G₁ := TranslationGroupoid.groupoid) (by infer_instance)
      (translationGroupoid_le_contDiffGroupoid n)
  exact IsManifold.mk' 𝓘(ℝ, Plane) n (Regular L₁ L₂ w)

theorem isManifold_smooth {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := isManifold hw₁ hw₂ ∞

end MNEC.RegularSmoothStructure
