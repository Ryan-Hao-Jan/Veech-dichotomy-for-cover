module

public import VeechDichotomy.OccupationPrimitive
public import VeechDichotomy.MonotoneRationalLimits

/-! Actual occupation profiles at positive rational multiples of a
reference time control source lengths with a varying positive ratio.
Both time directions supply all rational cumulative-primitive limits;
monotonicity then proves the required varying-endpoint convergence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingOccupationProfiles

open MeasureTheory Set Filter Topology OccupationPrimitive FlowIntegerAverages

abbrev PositiveRational := {a : ℚ // 0 < a}

variable {Ω : Type*} [TopologicalSpace Ω] (F : Flow ℝ Ω) (g : Ω → ℝ)

theorem rational_scaled {I : Type*} {l : Filter I} {R : I → ℝ} (hR : Tendsto R l atTop) (x : Ω) (m : ℝ)
    (hf : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F g ((a.val : ℝ) * R i) x) l (𝓝 m))
    (hb : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F.reverse g ((a.val : ℝ) * R i) x) l (𝓝 m)) :
    ∀ a : ℚ, Tendsto (fun i => scaled F g (R i) (a : ℝ) x) l (𝓝 ((a : ℝ) * m)) := by
  intro a
  have hRpos : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop (0 : ℝ))
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hlim : Tendsto (fun i => (a : ℝ) * timeAverage F.reverse g ((-(a : ℝ)) * R i) x) l (𝓝 ((a : ℝ) * m)) := by
      simpa only [Rat.cast_neg] using (hb ⟨-a, neg_pos.mpr ha⟩).const_mul (a : ℝ)
    apply Tendsto.congr' (h := hlim)
    filter_upwards [hRpos] with i hi
    exact (scaled_neg F g hi.ne' (Rat.cast_ne_zero.mpr ha.ne) x).symm
  · subst a
    simpa only [Rat.cast_zero, scaled_zero, zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) l (𝓝 0))
  · have hlim := (hf ⟨a, ha⟩).const_mul (a : ℝ)
    apply Tendsto.congr' (h := hlim)
    filter_upwards [hRpos] with i hi
    exact (scaled_pos F g hi.ne' (Rat.cast_ne_zero.mpr ha.ne') x).symm

variable [MeasurableSpace Ω] [BorelSpace Ω]

theorem varying_scaled (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (hpos : ∀ x, 0 ≤ g x)
    {I : Type*} {l : Filter I} {R : I → ℝ} (hR : Tendsto R l atTop) (x : Ω) (m : ℝ)
    (hf : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F g ((a.val : ℝ) * R i) x) l (𝓝 m))
    (hb : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F.reverse g ((a.val : ℝ) * R i) x) l (𝓝 m))
    {a : I → ℝ} {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun i => scaled F g (R i) (a i) x) l (𝓝 (a₀ * m)) := by
  have hRpos : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop (0 : ℝ))
  have hmono : ∀ᶠ i in l, Monotone (fun t => scaled F g (R i) t x) :=
    hRpos.mono (fun _ hi => monotone_scaled F g hg C hbound hpos hi x)
  exact MonotoneRationalLimits.varying_argument _ (fun t => t * m) hmono (rational_scaled F g hR x m hf hb) ha
    (continuous_id.mul continuous_const).continuousAt

theorem varying_timeAverage (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (hpos : ∀ x, 0 ≤ g x)
    {I : Type*} {l : Filter I} {R : I → ℝ} (hR : Tendsto R l atTop) (x : Ω) (m : ℝ)
    (hf : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F g ((a.val : ℝ) * R i) x) l (𝓝 m))
    (hb : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F.reverse g ((a.val : ℝ) * R i) x) l (𝓝 m))
    {T : I → ℝ} {a₀ : ℝ} (ha : Tendsto (fun i => T i / R i) l (𝓝 a₀)) (hapos : 0 < a₀) :
    Tendsto (fun i => timeAverage F g (T i) x) l (𝓝 m) := by
  have hv := (varying_scaled F g hg C hbound hpos hR x m hf hb ha).div ha hapos.ne'
  have heq : ∀ᶠ i in l, scaled F g (R i) (T i / R i) x / (T i / R i) = timeAverage F g (T i) x := by
    have hRpos : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hRpos] with i hi
    exact scaled_ratio F g hi.ne' (T i) x
  have hfinal : (a₀ * m) / a₀ = m := by field_simp [hapos.ne']
  simpa only [hfinal] using Tendsto.congr' heq hv

end VeechDichotomy.VaryingOccupationProfiles
