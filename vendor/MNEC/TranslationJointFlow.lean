module

public import MNEC.TranslationPartialFlow
public import MNEC.TranslationParameterizedWords

/-!
# Joint velocity, time and initial-point continuity of the native partial flow

A finite accepted word computes the reference time. One final physical
ball computes all nearby additional times. Word acceptance and evaluation
are continuous in velocity and point by their actual chart formulas. Native
autonomous laws identify this local model with the actual maximal curve.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationJointFlow

open LatticeTorus TranslationBallCharts TranslationFlowWords Set Topology Filter
open ParameterizedFlowWords (parameterSource parameterValue localValid localStep)
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

def valid : Set (Plane × ℝ × X) := {p | p.2.1 ∈ TranslationAtlasCurves.domain p.1 p.2.2}
def value (p : Plane × ℝ × X) : X := TranslationAtlasCurves.trajectory p.1 p.2.2 p.2.1

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X] [T2Space X]

set_option maxHeartbeats 300000 in
theorem valid_mem_nhds_and_continuousAt (v₀ : Plane) (t₀ : ℝ) (x₀ : X)
    (hvalid : t₀ ∈ TranslationAtlasCurves.domain v₀ x₀) :
    valid (X := X) ∈ 𝓝 ((v₀, t₀, x₀) : Plane × ℝ × X) ∧ ContinuousAt (value (X := X)) (v₀, t₀, x₀) := by
  obtain ⟨W, htime, hW⟩ := TranslationWordCoverage.word_of_mem_domain v₀ x₀ t₀ hvalid
  obtain ⟨B, hB⟩ := exists_ballChart_at (wordMap v₀ W x₀)
  let H : Plane × ℝ × X → Plane × ℝ × X := fun p => (p.1, p.2.1 - t₀, wordMap p.1 W p.2.2)
  have hVX : Continuous (fun p : Plane × ℝ × X => (p.1, p.2.2)) := continuous_fst.prodMk continuous_snd.snd
  have hWord : ContinuousAt (fun p : Plane × ℝ × X => wordMap p.1 W p.2.2) (v₀, t₀, x₀) := by
    have h0 := TranslationParameterizedWords.parameter_word_continuousAt W (v₀, x₀) hW
    exact ContinuousAt.comp (f := fun p : Plane × ℝ × X => (p.1, p.2.2)) (x := (v₀, t₀, x₀)) h0 hVX.continuousAt
  have hv : ContinuousAt (fun p : Plane × ℝ × X => p.1) (v₀, t₀, x₀) := continuous_fst.continuousAt
  have ht : ContinuousAt (fun p : Plane × ℝ × X => p.2.1 - t₀) (v₀, t₀, x₀) := (continuous_snd.fst.sub continuous_const).continuousAt
  have hH : ContinuousAt H (v₀, t₀, x₀) := hv.prodMk (ht.prodMk hWord)
  have hcenter : H (v₀, t₀, x₀) ∈ localValid (model B) := by
    change (v₀, t₀ - t₀, wordMap v₀ W x₀) ∈ localValid (model B)
    rw [sub_self]
    exact ParameterizedFlowWords.zero_mem_localValid (model B) v₀ (wordMap v₀ W x₀) hB
  have hnearW : ∀ᶠ p in 𝓝 ((v₀, t₀, x₀) : Plane × ℝ × X), p.2.2 ∈ (wordMap p.1 W).source := by
    have hxW : ((v₀, x₀) : Plane × X) ∈ parameterSource (fun v => wordMap v W) := hW
    have hmem : parameterSource (fun v => wordMap v W) ∈ 𝓝 ((v₀, x₀) : Plane × X) :=
      (TranslationParameterizedWords.parameter_word W).1.mem_nhds hxW
    exact (hVX.continuousAt (x := (v₀, t₀, x₀))) hmem
  have hnearB : ∀ᶠ p in 𝓝 ((v₀, t₀, x₀) : Plane × ℝ × X), H p ∈ localValid (model B) :=
    hH ((ParameterizedFlowWords.localValid_open (model B)).mem_nhds hcenter)
  have hnear : ∀ᶠ p in 𝓝 ((v₀, t₀, x₀) : Plane × ℝ × X), p ∈ valid ∧ value p = localStep (model B) (H p) := by
    filter_upwards [hnearW, hnearB] with p hpW hpB
    have htW : t₀ ∈ TranslationAtlasCurves.domain p.1 p.2.2 := by
      have h := word_time_mem_domain p.1 W p.2.2 hpW
      rwa [htime] at h
    have hvalue : wordMap p.1 W p.2.2 = TranslationAtlasCurves.trajectory p.1 p.2.2 t₀ := by
      have h := wordMap_eq_trajectory p.1 W p.2.2 hpW
      rwa [htime] at h
    have hstep : wordMap p.1 W p.2.2 ∈ (timeMap B p.1 (p.2.1 - t₀)).source :=
      (TranslationParameterizedWords.ball_localValid_iff B (H p)).mp hpB
    obtain ⟨hdelta, hstepValue⟩ := timeMap_native_identification B p.1 (p.2.1 - t₀) (wordMap p.1 W p.2.2) hstep
    have hδ : p.2.1 - t₀ ∈ TranslationAtlasCurves.domain p.1 (TranslationAtlasCurves.trajectory p.1 p.2.2 t₀) := by
      rw [← hvalue]
      exact hdelta
    have ht : p.2.1 ∈ TranslationAtlasCurves.domain p.1 p.2.2 := by
      have h := hδ
      rw [TranslationAtlasCurves.domain_at_time p.1 p.2.2 t₀ htW] at h
      change (p.2.1 - t₀) + t₀ ∈ TranslationAtlasCurves.domain p.1 p.2.2 at h
      simpa only [sub_add_cancel] using h
    refine ⟨ht, ?_⟩
    symm
    calc
      localStep (model B) (H p) = TranslationAtlasCurves.trajectory p.1 (wordMap p.1 W p.2.2) (p.2.1 - t₀) := hstepValue
      _ = TranslationAtlasCurves.trajectory p.1 (TranslationAtlasCurves.trajectory p.1 p.2.2 t₀) (p.2.1 - t₀) := by rw [hvalue]
      _ = TranslationAtlasCurves.trajectory p.1 p.2.2 ((p.2.1 - t₀) + t₀) :=
        TranslationAtlasCurves.trajectory_add p.1 p.2.2 t₀ htW (p.2.1 - t₀) hδ
      _ = value p := by rw [sub_add_cancel]; rfl
  have hcontinuous : ContinuousAt (fun p => localStep (model B) (H p)) (v₀, t₀, x₀) :=
    ContinuousAt.comp (f := H) (x := (v₀, t₀, x₀))
      (ParameterizedFlowWords.continuousAt_localStep (model B) (H (v₀, t₀, x₀)) hcenter) hH
  exact ⟨Filter.mem_of_superset hnear (fun _ h => h.1),
    hcontinuous.congr_of_eventuallyEq (Filter.mem_of_superset hnear (fun _ h => h.2))⟩

theorem valid_open : IsOpen (valid (X := X)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨v, t, x⟩ h
  exact (valid_mem_nhds_and_continuousAt v t x h).1

theorem continuousAt_value (p : Plane × ℝ × X) (hp : p ∈ valid) : ContinuousAt (value (X := X)) p :=
  (valid_mem_nhds_and_continuousAt p.1 p.2.1 p.2.2 hp).2

theorem continuousOn_value : ContinuousOn (value (X := X)) valid := fun p hp => (continuousAt_value p hp).continuousWithinAt

end MNEC.TranslationJointFlow

