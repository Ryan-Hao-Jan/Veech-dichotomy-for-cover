module

public import VeechDichotomy.HyperbolicDirichletCorners
public import Mathlib.Topology.Order.IntermediateValue

/-! A continuous injective real curve in a genuine affine complex line
maps every unordered parameter interval onto the Euclidean segment of
its endpoints. A perpendicular coordinate is injective on that line;
the actual one-dimensional intermediate value theorem supplies the
entire interval, including its order in either orientation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexAffineLineSegments

open Set

def normal (a b : ℝ) : ℂ →L[ℝ] ℝ := a • Complex.reCLM + b • Complex.imCLM

def coordinate (a b : ℝ) : ℂ →L[ℝ] ℝ := (-b) • Complex.reCLM + a • Complex.imCLM

def affineLine (a b c : ℝ) : Set ℂ := {z | normal a b z = c}

theorem convex_affineLine (a b c : ℝ) : Convex ℝ (affineLine a b c) :=
  (convex_singleton c).linear_preimage (normal a b).toLinearMap

theorem coordinate_injOn (a b c : ℝ) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    InjOn (coordinate a b) (affineLine a b c) := by
  intro u hu v hv he
  have hd : a * a - (-b) * b ≠ 0 := by
    convert hab using 1
    ring
  apply HyperbolicDirichletCorners.affine_intersection_subsingleton (-c) a b
    (-(coordinate a b u)) (-b) a hd
  · change -c + a * u.re + b * u.im = 0 ∧
      -(coordinate a b u) + -b * u.re + a * u.im = 0
    simp only [affineLine, mem_ofPred_eq, normal, coordinate, add_apply, smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul] at hu ⊢
    constructor <;> linarith
  · change -c + a * v.re + b * v.im = 0 ∧
      -(coordinate a b u) + -b * v.re + a * v.im = 0
    simp only [affineLine, mem_ofPred_eq, normal, coordinate, add_apply, smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul] at hv he ⊢
    constructor <;> linarith

theorem image_interval (f : ℝ → ℂ) (hf : Continuous f) (hi : Function.Injective f)
    (a b c : ℝ) (hab : a ^ 2 + b ^ 2 ≠ 0)
    (hline : ∀ t, f t ∈ affineLine a b c) (s t : ℝ) :
    f '' uIcc s t = segment ℝ (f s) (f t) := by
  let g : ℝ → ℝ := fun u => coordinate a b (f u)
  have hg : Continuous g := (coordinate a b).continuous.comp hf
  have hgi : Function.Injective g := fun u v huv =>
    hi (coordinate_injOn a b c hab (hline u) (hline v) huv)
  have hgImage : g '' uIcc s t = uIcc (g s) (g t) := by
    rcases hg.strictMono_of_inj hgi with hm | hm
    · exact hg.continuousOn.image_uIcc_of_monotoneOn (hm.monotone.monotoneOn _)
    · exact hg.continuousOn.image_uIcc_of_antitoneOn (hm.antitone.antitoneOn _)
  have hseg : segment ℝ (f s) (f t) ⊆ affineLine a b c :=
    (convex_affineLine a b c).segment_subset (hline s) (hline t)
  have hc : coordinate a b '' segment ℝ (f s) (f t) = uIcc (g s) (g t) := by
    change (coordinate a b).toLinearMap.toAffineMap '' segment ℝ (f s) (f t) = _
    rw [image_segment, segment_eq_uIcc]
    rfl
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hgu : g u ∈ uIcc (g s) (g t) := hgImage ▸ mem_image_of_mem g hu
    obtain ⟨w, hw, he⟩ := hc.symm ▸ hgu
    have hwu : w = f u := coordinate_injOn a b c hab (hseg hw) (hline u) he
    exact hwu ▸ hw
  · intro z hz
    have hcz : coordinate a b z ∈ uIcc (g s) (g t) := hc ▸ mem_image_of_mem _ hz
    obtain ⟨u, hu, he⟩ := hgImage.symm ▸ hcz
    exact ⟨u, hu, coordinate_injOn a b c hab (hline u) (hseg hz) he⟩

end VeechDichotomy.ComplexAffineLineSegments
