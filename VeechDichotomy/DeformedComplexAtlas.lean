module

public import VeechDichotomy.DeformedRegularAtlas

/-! The genuine complex manifold structure on the SL2-deformed regular
locus. Its complex chart transitions are locally translations, hence
holomorphic, because the real linear transformation conjugates each old
translation to another translation.

No extension over the finite punctures is asserted in this file.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DeformedComplexAtlas

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open DeformedRegularAtlas LinearEquivalences LinearGroup Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

def complexChart (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    OpenPartialHomeomorph (DeformedRegular q A) ℂ :=
  (chart q A i).transHomeomorph toPlane.symm.toHomeomorph

theorem complexChart_source (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    (complexChart q A i).source = (chart q A i).source := rfl

theorem complexChart_target (q : Differential X) (A : SL2) (i : DeformedRegular q A) :
    (complexChart q A i).target = toPlane ⁻¹' (chart q A i).target := rfl

theorem complexChart_apply (q : Differential X) (A : SL2) (i p : DeformedRegular q A) :
    complexChart q A i p = toPlane.symm (chart q A i p) := rfl

@[instance_reducible] def chartedSpace (q : Differential X) (A : SL2) :
    ChartedSpace ℂ (DeformedRegular q A) where
  atlas := range (complexChart q A)
  chartAt := complexChart q A
  mem_chart_source := DeformedRegularAtlas.chart_center q A
  chart_mem_atlas i := ⟨i, rfl⟩

theorem transition_formula (q : Differential X) (A : SL2) (i j : DeformedRegular q A)
    (z : ℂ) :
    ((complexChart q A i).symm.trans (complexChart q A j)) z =
      toPlane.symm (((chart q A i).symm.trans (chart q A j)) (toPlane z)) := rfl

theorem transition_germ (q : Differential X) (A : SL2) (i j : DeformedRegular q A)
    (z : ℂ) (hz : z ∈ ((complexChart q A i).symm.trans (complexChart q A j)).source) :
    ∃ a : ℂ, ∀ᶠ w in 𝓝 z,
      ((complexChart q A i).symm.trans (complexChart q A j)) w = w + a := by
  have hp : toPlane z ∈ ((chart q A i).symm.trans (chart q A j)).source := hz
  obtain ⟨a, ha⟩ := DeformedRegularAtlas.transition_locally_translation q A i j (toPlane z) hp
  have hc : ContinuousAt toPlane z := toPlane.continuous.continuousAt
  refine ⟨toPlane.symm a, ?_⟩
  filter_upwards [hc ha] with w hw
  rw [transition_formula, hw, map_add, ContinuousLinearEquiv.symm_apply_apply]

theorem transition_contDiffOn (q : Differential X) (A : SL2) (n : ℕ∞ω)
    (i j : DeformedRegular q A) :
    ContDiffOn ℂ n ((complexChart q A i).symm.trans (complexChart q A j))
      ((complexChart q A i).symm.trans (complexChart q A j)).source := by
  intro z hz
  obtain ⟨a, ha⟩ := transition_germ q A i j z hz
  exact ((contDiff_id.add contDiff_const).contDiffAt.congr_of_eventuallyEq ha).contDiffWithinAt

theorem has_complex_groupoid (q : Differential X) (A : SL2) (n : ℕ∞ω) :
    letI := chartedSpace q A
    HasGroupoid (DeformedRegular q A) (contDiffGroupoid n 𝓘(ℂ)) := by
  let := chartedSpace q A
  apply hasGroupoid_of_pregroupoid (contDiffPregroupoid n 𝓘(ℂ))
  intro e f he hf
  change e ∈ range (complexChart q A) at he
  change f ∈ range (complexChart q A) at hf
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hf
  simpa only [contDiffPregroupoid, mfld_simps] using transition_contDiffOn q A n i j

theorem isComplexManifold (q : Differential X) (A : SL2) (n : ℕ∞ω) :
    letI := chartedSpace q A
    IsManifold 𝓘(ℂ) n (DeformedRegular q A) := by
  let := chartedSpace q A
  let : HasGroupoid (DeformedRegular q A) (contDiffGroupoid n 𝓘(ℂ)) :=
    has_complex_groupoid q A n
  exact IsManifold.mk' 𝓘(ℂ) n (DeformedRegular q A)

end VeechDichotomy.DeformedComplexAtlas
