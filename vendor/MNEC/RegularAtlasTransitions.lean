module

public import MNEC.RegularAtlasCoverage
public import MNEC.SeamChartCoordinates
public import MNEC.LocalPeriods

/-!
# All regular physical chart transitions are locally translations

The actual quotient off-trace distinguishes the two torus pieces. Near an
off-seam overlap, the two physical coordinate maps project to the same
specified lattice torus, so their continuous difference is locally one
actual period. At the seam axis the proved transition is identity.
-/

noncomputable section
@[expose] public section

namespace MNEC.RegularAtlasTransitions

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts SlitConnectedSum
open SeamChartMaps SeamChartOffAxis SeamCharts SeamChartCoordinates RegularAtlasCoverage
open Set Topology Filter
open scoped Classical

theorem offTrace_left_upper (L₁ L₂ : Lattice) (w : Plane) (u : Torus)
    (hu : u ∉ L₁.slitSet w) :
    offTrace L₁ L₂ w (left L₁ L₂ w (upper L₁ w u)) = some (Sum.inl u) := by
  change (if u ∈ L₁.slitSet w then none else some (Sum.inl u)) = some (Sum.inl u)
  exact ite_eq_right hu

theorem offTrace_right_upper (L₁ L₂ : Lattice) (w : Plane) (u : Torus)
    (hu : u ∉ L₂.slitSet w) :
    offTrace L₁ L₂ w (right L₁ L₂ w (upper L₂ w u)) = some (Sum.inr u) := by
  change (if u ∈ L₂.slitSet w then none else some (Sum.inr u)) = some (Sum.inr u)
  exact ite_eq_right hu

theorem leftChart_trace {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (a p : Plane)
    (hp : p ∈ (RegularAtlasCoverage.chart hw₁ hw₂ (.left a)).source) :
    offTrace L₁ L₂ w (RegularAtlasCoverage.chart hw₁ hw₂ (.left a) p) =
      some (Sum.inl (L₁.project p)) := by
  change offTrace L₁ L₂ w
    (OffSlitCharts.leftChart L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a p) = _
  rw [OffSlitCharts.leftChart_apply L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a p hp]
  exact offTrace_left_upper L₁ L₂ w _
    (((OffSlitCharts.leftChart_source L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a) ▸ hp).2)

theorem rightChart_trace {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (a p : Plane)
    (hp : p ∈ (RegularAtlasCoverage.chart hw₁ hw₂ (.right a)).source) :
    offTrace L₁ L₂ w (RegularAtlasCoverage.chart hw₁ hw₂ (.right a) p) =
      some (Sum.inr (L₂.project p)) := by
  change offTrace L₁ L₂ w
    (OffSlitCharts.rightChart L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a p) = _
  rw [OffSlitCharts.rightChart_apply L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a p hp]
  exact offTrace_right_upper L₁ L₂ w _
    (((OffSlitCharts.rightChart_source L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a) ▸ hp).2)

theorem seamChart_trace_positive {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hpos : 0 < (coordinates hw₁ k p).2) :
    offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = some (Sum.inl (L₁.project p)) := by
  rw [SeamChartCoordinates.physicalChart_apply hw₁ hw₂ C k p hp,
    chart_positive_off C (embeddedSlit_ne_zero L₁ w hw₁) k
      ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ hpos,
    offTrace_leftOff]
  simp only [coordinates, Homeomorph.apply_symm_apply]

theorem seamChart_trace_negative {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source)
    (hneg : (coordinates hw₁ k p).2 < 0) :
    offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = some (Sum.inr (L₂.project p)) := by
  rw [SeamChartCoordinates.physicalChart_apply hw₁ hw₂ C k p hp,
    chart_negative_off C (embeddedSlit_ne_zero L₁ w hw₁) k
      ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ hneg,
    offTrace_rightOff]
  simp only [coordinates, Homeomorph.apply_symm_apply]

theorem chart_axis_of_trace_none {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ (RegularAtlasCoverage.chart hw₁ hw₂ i).source)
    (htrace : offTrace L₁ L₂ w (RegularAtlasCoverage.chart hw₁ hw₂ i p) = none) :
    ∃ C k, i = .seam C k ∧ (coordinates hw₁ k p).2 = 0 := by
  cases i with
  | left a => rw [leftChart_trace hw₁ hw₂ a p hp] at htrace; cases htrace
  | right a => rw [rightChart_trace hw₁ hw₂ a p hp] at htrace; cases htrace
  | seam C k =>
    change offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = none at htrace
    change p ∈ (physicalChart hw₁ hw₂ C k).source at hp
    exact ⟨C, k, rfl, (offTrace_physicalChart_eq_none_iff hw₁ hw₂ C k p hp).1 htrace⟩

theorem chart_eventually_left_of_trace {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ (RegularAtlasCoverage.chart hw₁ hw₂ i).source) (t : Torus)
    (htrace : offTrace L₁ L₂ w (RegularAtlasCoverage.chart hw₁ hw₂ i p) = some (Sum.inl t)) :
    ∀ᶠ y in 𝓝 p, RegularAtlasCoverage.chart hw₁ hw₂ i y =
      left L₁ L₂ w (upper L₁ w (L₁.project y)) := by
  cases i with
  | left a =>
    filter_upwards [(RegularAtlasCoverage.chart hw₁ hw₂ (.left a)).open_source.mem_nhds hp]
      with y hy
    exact OffSlitCharts.leftChart_apply L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a y hy
  | right a => rw [rightChart_trace hw₁ hw₂ a p hp] at htrace; cases htrace
  | seam C k =>
    change offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = some (Sum.inl t) at htrace
    change p ∈ (physicalChart hw₁ hw₂ C k).source at hp
    have hne : (coordinates hw₁ k p).2 ≠ 0 := by
      intro hz
      rw [(offTrace_physicalChart_eq_none_iff hw₁ hw₂ C k p hp).2 hz] at htrace
      cases htrace
    have hpos : 0 < (coordinates hw₁ k p).2 := by
      rcases lt_or_gt_of_ne hne with hn | hpos
      · rw [seamChart_trace_negative hw₁ hw₂ C k p hp hn] at htrace
        cases htrace
      · exact hpos
    have hc : Continuous (fun y : Plane => (coordinates hw₁ k y).2) :=
      continuous_snd.comp (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm.continuous
    have hsign : ∀ᶠ y in 𝓝 p, 0 < (coordinates hw₁ k y).2 :=
      hc.continuousAt (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [(physicalChart hw₁ hw₂ C k).open_source.mem_nhds hp, hsign] with y hy hs
    exact physicalChart_positive hw₁ hw₂ C k y hy hs

theorem chart_eventually_right_of_trace {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ (RegularAtlasCoverage.chart hw₁ hw₂ i).source) (t : Torus)
    (htrace : offTrace L₁ L₂ w (RegularAtlasCoverage.chart hw₁ hw₂ i p) = some (Sum.inr t)) :
    ∀ᶠ y in 𝓝 p, RegularAtlasCoverage.chart hw₁ hw₂ i y =
      right L₁ L₂ w (upper L₂ w (L₂.project y)) := by
  cases i with
  | left a => rw [leftChart_trace hw₁ hw₂ a p hp] at htrace; cases htrace
  | right a =>
    filter_upwards [(RegularAtlasCoverage.chart hw₁ hw₂ (.right a)).open_source.mem_nhds hp]
      with y hy
    exact OffSlitCharts.rightChart_apply L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a y hy
  | seam C k =>
    change offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) = some (Sum.inr t) at htrace
    change p ∈ (physicalChart hw₁ hw₂ C k).source at hp
    have hne : (coordinates hw₁ k p).2 ≠ 0 := by
      intro hz
      rw [(offTrace_physicalChart_eq_none_iff hw₁ hw₂ C k p hp).2 hz] at htrace
      cases htrace
    have hneg : (coordinates hw₁ k p).2 < 0 := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact hneg
      · rw [seamChart_trace_positive hw₁ hw₂ C k p hp hpos] at htrace
        cases htrace
    have hc : Continuous (fun y : Plane => (coordinates hw₁ k y).2) :=
      continuous_snd.comp (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm.continuous
    have hsign : ∀ᶠ y in 𝓝 p, (coordinates hw₁ k y).2 < 0 :=
      hc.continuousAt (isOpen_Iio.mem_nhds hneg)
    filter_upwards [(physicalChart hw₁ hw₂ C k).open_source.mem_nhds hp, hsign] with y hy hs
    exact physicalChart_negative hw₁ hw₂ C k y hy hs

/-- Every transition in the constructed regular physical chart family is locally a translation. -/
theorem transition_locally_translation {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i j : Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ ((RegularAtlasCoverage.chart hw₁ hw₂ i).trans
      (RegularAtlasCoverage.chart hw₁ hw₂ j).symm).source) :
    ∃ v : Plane, ∀ᶠ y in 𝓝 p,
      ((RegularAtlasCoverage.chart hw₁ hw₂ i).trans
        (RegularAtlasCoverage.chart hw₁ hw₂ j).symm) y = y + v := by
  let e := RegularAtlasCoverage.chart hw₁ hw₂ i
  let d := RegularAtlasCoverage.chart hw₁ hw₂ j
  let F := e.trans d.symm
  have hpA : p ∈ e.source := hp.1
  have hpB : e p ∈ d.target := hp.2
  have hFp : F p ∈ d.source := d.map_target hpB
  have heq : e p = d (F p) := (d.right_inv hpB).symm
  have hF : ContinuousAt F p := F.continuousAt hp
  cases htrace : offTrace L₁ L₂ w (e p) with
  | none =>
    have hdtrace : offTrace L₁ L₂ w (d (F p)) = none :=
      (congrArg (offTrace L₁ L₂ w) heq).symm.trans htrace
    obtain ⟨C, k, rfl, hz⟩ := chart_axis_of_trace_none hw₁ hw₂ i p hpA htrace
    obtain ⟨D, l, rfl, _⟩ := chart_axis_of_trace_none hw₁ hw₂ j (F p) hFp hdtrace
    obtain ⟨U, hU, hpU, _, hidentity⟩ :=
      physical_transition_identity_near_axis hw₁ hw₂ C D k l p (F p) hpA hFp hz heq
    refine ⟨0, ?_⟩
    filter_upwards [hU.mem_nhds hpU] with y hy
    change (physicalChart hw₁ hw₂ D l).symm (physicalChart hw₁ hw₂ C k y) = y + (0 : Plane)
    simpa only [add_zero] using hidentity y hy
  | some v =>
    cases v with
    | inl t =>
      have hdtrace : offTrace L₁ L₂ w (d (F p)) = some (Sum.inl t) :=
        (congrArg (offTrace L₁ L₂ w) heq).symm.trans htrace
      have hevent := chart_eventually_left_of_trace hw₁ hw₂ i p hpA t htrace
      have hdevent := chart_eventually_left_of_trace hw₁ hw₂ j (F p) hFp t hdtrace
      have hproj : ∀ᶠ y in 𝓝 p, L₁.project (F y) = L₁.project y := by
        filter_upwards [hevent, hF hdevent, F.open_source.mem_nhds hp] with y hy hd hyF
        have heqy : e y = d (F y) := (d.right_inv hyF.2).symm
        have hcut := SeamClasses.left_injective L₁ L₂ w hw₁ hw₂ (hy.symm.trans (heqy.trans hd))
        exact (congrArg base hcut).symm
      obtain ⟨z, hz⟩ := LocalPeriods.locally_translation_of_eventually_project_eq L₁ F p hF hproj
      exact ⟨L₁.period z, hz⟩
    | inr t =>
      have hdtrace : offTrace L₁ L₂ w (d (F p)) = some (Sum.inr t) :=
        (congrArg (offTrace L₁ L₂ w) heq).symm.trans htrace
      have hevent := chart_eventually_right_of_trace hw₁ hw₂ i p hpA t htrace
      have hdevent := chart_eventually_right_of_trace hw₁ hw₂ j (F p) hFp t hdtrace
      have hproj : ∀ᶠ y in 𝓝 p, L₂.project (F y) = L₂.project y := by
        filter_upwards [hevent, hF hdevent, F.open_source.mem_nhds hp] with y hy hd hyF
        have heqy : e y = d (F y) := (d.right_inv hyF.2).symm
        have hcut := SeamClasses.right_injective L₁ L₂ w hw₁ hw₂ (hy.symm.trans (heqy.trans hd))
        exact (congrArg base hcut).symm
      obtain ⟨z, hz⟩ := LocalPeriods.locally_translation_of_eventually_project_eq L₂ F p hF hproj
      exact ⟨L₂.period z, hz⟩

end MNEC.RegularAtlasTransitions
