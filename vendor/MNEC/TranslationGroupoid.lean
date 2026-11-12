module

public import MNEC.LatticeTorus
public import Mathlib.Geometry.Manifold.StructureGroupoid

/-!
# The native structure groupoid of local plane translations

The pregroupoid property is an actual neighborhood equality with a
translation. Composition, locality, and invariance under equality on open
sets are proved, and mathlib constructs the inverse-stable groupoid.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationGroupoid

open LatticeTorus Set Topology Filter

def LocallyTranslationOn (f : Plane → Plane) (u : Set Plane) : Prop :=
  ∀ x ∈ u, ∃ v : Plane, ∀ᶠ y in 𝓝 x, f y = y + v

theorem continuousAt_of_local_translation {f : Plane → Plane} {x : Plane}
    (h : ∃ v : Plane, ∀ᶠ y in 𝓝 x, f y = y + v) : ContinuousAt f x := by
  obtain ⟨v, hv⟩ := h
  exact (continuous_id.add continuous_const).continuousAt.congr_of_eventuallyEq hv

theorem locallyTranslationOn_comp {f g : Plane → Plane} {u v : Set Plane}
    (hf : LocallyTranslationOn f u) (hg : LocallyTranslationOn g v) :
    LocallyTranslationOn (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x hx
  obtain ⟨a, ha⟩ := hf x hx.1
  obtain ⟨b, hb⟩ := hg (f x) hx.2
  have hcont : ContinuousAt f x := continuousAt_of_local_translation ⟨a, ha⟩
  refine ⟨a + b, ?_⟩
  filter_upwards [ha, hcont hb] with y hy hgy
  rw [Function.comp_apply, hgy, hy, add_assoc]

theorem locallyTranslationOn_mono {f : Plane → Plane} {u v : Set Plane}
    (h : LocallyTranslationOn f v) (huv : u ⊆ v) : LocallyTranslationOn f u :=
  fun x hx => h x (huv hx)

theorem locallyTranslationOn_congr {f g : Plane → Plane} {u : Set Plane}
    (hu : IsOpen u) (hgf : ∀ x ∈ u, g x = f x) (hf : LocallyTranslationOn f u) :
    LocallyTranslationOn g u := by
  intro x hx
  obtain ⟨v, hv⟩ := hf x hx
  refine ⟨v, ?_⟩
  filter_upwards [hu.mem_nhds hx, hv] with y hy hfy
  exact (hgf y hy).trans hfy

def pregroupoid : Pregroupoid Plane where
  property := LocallyTranslationOn
  comp := fun hf hg _ _ _ => locallyTranslationOn_comp hf hg
  id_mem := by
    intro x _
    exact ⟨0, Filter.Eventually.of_forall (fun y => by simp)⟩
  locality := by
    intro f u _ h x hx
    obtain ⟨v, _, hxv, hf⟩ := h x hx
    exact hf x ⟨hx, hxv⟩
  congr := fun hu hgf hf => locallyTranslationOn_congr hu hgf hf

def groupoid : StructureGroupoid Plane := pregroupoid.groupoid

theorem mem_groupoid_iff (e : OpenPartialHomeomorph Plane Plane) :
    e ∈ groupoid ↔ LocallyTranslationOn e e.source ∧ LocallyTranslationOn e.symm e.target :=
  Iff.rfl

end MNEC.TranslationGroupoid
