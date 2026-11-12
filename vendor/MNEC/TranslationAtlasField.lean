module

public import MNEC.FlatChartDerivatives

/-!
# A genuine smooth physical vector field on any native translation atlas

The only geometric inputs are the native charted structure, its proved
translation groupoid, and its native smooth manifold instance. Chart
derivatives are proved to be identity maps, and native bundle smoothness
of the constructed pullback field follows from actual trivializations.
No smooth-vector-field or directional-flow hypothesis is assumed.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationAtlasField

open LatticeTorus Set Topology Filter
open scoped Manifold ContDiff Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]
variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X]

omit [IsManifold 𝓘(ℝ, Plane) ∞ X] in
theorem transition_hasFDerivAt (e f : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (hf : f ∈ atlas Plane X) (p : Plane)
    (hp : p ∈ (e.symm.trans f).source) :
    HasFDerivAt (e.symm.trans f) (ContinuousLinearMap.id ℝ Plane) p := by
  have hgroup := TranslationGroupoid.groupoid.compatible he hf
  have htrans := ((TranslationGroupoid.mem_groupoid_iff _).mp hgroup).1
  obtain ⟨v, hv⟩ := htrans p hp
  exact ((hasFDerivAt_id p).add_const v).congr_of_eventuallyEq hv

theorem mfderiv_atlas_id (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (x : X) (hx : x ∈ e.source) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e x = ContinuousLinearMap.id ℝ Plane := by
  let c := chartAt Plane x
  have hxc : x ∈ c.source := mem_chart_source Plane x
  have hp : c x ∈ (c.symm.trans e).source := by
    refine ⟨c.map_source hxc, ?_⟩
    change c.symm (c x) ∈ e.source
    rw [c.left_inv hxc]
    exact hx
  have htransition := (transition_hasFDerivAt c e (chart_mem_atlas Plane x) he (c x) hp).fderiv
  have hdiff := mdifferentiableAt_atlas (I := 𝓘(ℝ, Plane)) he hx
  rw [hdiff.mfderiv_abuse]
  simpa only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ, c] using! htransition

theorem mfderiv_atlas_symm_id (e : OpenPartialHomeomorph X Plane) (he : e ∈ atlas Plane X)
    (y : Plane) (hy : y ∈ e.target) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e.symm y = ContinuousLinearMap.id ℝ Plane := by
  have hdiff : e.MDifferentiable 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) := mdifferentiable_of_mem_atlas he
  have hcomp := hdiff.comp_symm_deriv hy
  rw [mfderiv_atlas_id e he (e.symm y) (e.map_target hy)] at hcomp
  simpa only [ContinuousLinearMap.id_comp] using! hcomp

theorem tangentCoordChange_id (x y : X) (hy : y ∈ (chartAt Plane x).source) :
    tangentCoordChange 𝓘(ℝ, Plane) y x y = ContinuousLinearMap.id ℝ Plane := by
  rw [← mfderiv_chartAt_eq_tangentCoordChange hy]
  exact mfderiv_atlas_id (chartAt Plane x) (chart_mem_atlas Plane x) y hy

/-- Native pullback of the constant physical velocity through the actual
preferred chart at the point. Independence of this choice is proved below. -/
def field (v : Plane) : ∀ x : X, TangentSpace 𝓘(ℝ, Plane) x :=
  fun x => VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x) (fun _ : Plane => v) x

theorem field_eq_const (v : Plane) (x : X) : field v x = v := by
  unfold field VectorField.mpullback
  rw [mfderiv_atlas_id (chartAt Plane x) (chart_mem_atlas Plane x) x (mem_chart_source Plane x)]
  have hid : (ContinuousLinearMap.id ℝ Plane).inverse v = v := by
    rw [ContinuousLinearMap.inverse_id]
    rfl
  simpa only [] using! hid

theorem field_eq_pullback_in_chart (v : Plane) (e : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (x : X) (hx : x ∈ e.source) :
    field v x = VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (fun _ : Plane => v) x := by
  rw [field_eq_const]
  unfold VectorField.mpullback
  rw [mfderiv_atlas_id e he x hx]
  have hid : v = (ContinuousLinearMap.id ℝ Plane).inverse v := by
    rw [ContinuousLinearMap.inverse_id]
    rfl
  simpa only [] using! hid

/-- The intrinsic field has physical coordinate vector `v` in every actual
chart of the native translation atlas. -/
theorem coordinate_formula (v : Plane) (e : OpenPartialHomeomorph X Plane)
    (he : e ∈ atlas Plane X) (x : X) (hx : x ∈ e.source) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e x (field v x) = v := by
  rw [mfderiv_atlas_id e he x hx, field_eq_const]
  rfl

theorem trivialization_formula (v : Plane) (x y : X) (hy : y ∈ (chartAt Plane x).source) :
    (trivializationAt Plane (TangentSpace 𝓘(ℝ, Plane)) x
      (⟨y, field v y⟩ : TangentBundle 𝓘(ℝ, Plane) X)).2 = v := by
  rw [TangentBundle.trivializationAt_apply]
  change tangentCoordChange 𝓘(ℝ, Plane) y x y (field v y) = v
  rw [tangentCoordChange_id x y hy, field_eq_const]
  rfl

/-- Smoothness of the actual section into the native tangent bundle. -/
theorem contMDiff_field (v : Plane) :
    ContMDiff 𝓘(ℝ, Plane) (𝓘(ℝ, Plane)).tangent ∞
      (fun x : X => (⟨x, field v x⟩ : TangentBundle 𝓘(ℝ, Plane) X)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  apply contMDiffAt_const.congr_of_eventuallyEq
  filter_upwards [(chartAt Plane x).open_source.mem_nhds (mem_chart_source Plane x)] with y hy
  exact trivialization_formula v x y hy

theorem contMDiff_field_one (v : Plane) :
    ContMDiff 𝓘(ℝ, Plane) (𝓘(ℝ, Plane)).tangent 1
      (fun x : X => (⟨x, field v x⟩ : TangentBundle 𝓘(ℝ, Plane) X)) :=
  (contMDiff_field v).of_le (by simp)

end MNEC.TranslationAtlasField

