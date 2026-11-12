module

public import MNEC.SlitCollars

@[expose] public section

/-!
# Continuous lifts of the same torus map differ locally by one period

The period is constructed from the actual quotient kernel. A physical
quotient chart then makes that period locally constant. This supplies the
translation-transition step without assuming a discrete-period assertion.
-/

noncomputable section

namespace MNEC.LocalPeriods

open LatticeTorus SlitCollars Filter Set
open scoped Topology

theorem locally_translation_of_eventually_project_eq (L : Lattice)
    (F : Plane → Plane) (p : Plane) (hF : ContinuousAt F p)
    (hproj : ∀ᶠ y in 𝓝 p, L.project (F y) = L.project y) :
    ∃ z : ℤ × ℤ, ∀ᶠ y in 𝓝 p, F y = y + L.period z := by
  have hp : L.project (F p) = L.project p := hproj.self_of_nhds
  obtain ⟨z, hz⟩ := (L.project_eq_iff (F p) p).mp hp
  have htranslate : F p = p + L.period z := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hz
  have hperiod : L.project (L.period z) = 0 :=
    (L.project_eq_zero_iff _).mpr ⟨z, rfl⟩
  let a := chartOrigin L (F p)
  have hcenter : F p ∈ (torusChart L a).source := mem_center_chart L (F p)
  have hsourceF : ∀ᶠ y in 𝓝 p, F y ∈ (torusChart L a).source :=
    hF ((torusChart L a).open_source.mem_nhds hcenter)
  have htransCont : Continuous (fun y : Plane => y + L.period z) :=
    continuous_id.add continuous_const
  have hsourceTranslation : ∀ᶠ y in 𝓝 p, y + L.period z ∈ (torusChart L a).source := by
    apply htransCont.continuousAt
    apply (torusChart L a).open_source.mem_nhds
    change p + L.period z ∈ (torusChart L a).source
    rw [← htranslate]
    exact hcenter
  refine ⟨z, ?_⟩
  filter_upwards [hproj, hsourceF, hsourceTranslation] with y hy hFy hty
  apply projection_injOn_chart L a hFy hty
  rw [L.project_add, hperiod, add_zero]
  exact hy

end MNEC.LocalPeriods
