module

public import VeechDichotomy.NativeAffinePrimitiveGerms
public import VeechDichotomy.NativePowerCharts
public import VeechDichotomy.PuncturedDiskConstancy

/-! An actual native affine automorphism fixing a point acts linearly
on the genuine local power primitive there, INCLUDING at a zero.
Regular primitive germs make the error locally constant off the center;
punctured-disk connectedness and actual continuity force zero error. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAffinePowerGerms

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativePowerCharts NativeVeech LinearGroup Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {A : SL2} (φ : AffineAutomorphism q A)

theorem fixed_point_germ (b : X) (P : PowerChart q b) (hfix : φ.surface b = b) :
    ∀ᶠ y in 𝓝 b, toPlane (P.chart (φ.surface y) ^ P.exponent) =
      linear A (toPlane (P.chart y ^ P.exponent)) := by
  let c := P.chart
  let F : X → ℂ := fun y => c y ^ P.exponent
  let H : X → Plane := fun y => toPlane (F (φ.surface y)) - linear A (toPlane (F y))
  let g : ℂ → Plane := fun z => H (c.symm z)
  have hb : b ∈ c.source := P.center
  have hc0 : c b = 0 := P.center_zero
  have hct : (0 : ℂ) ∈ c.target := by simpa only [hc0] using c.map_source hb
  have hinv0 : c.symm 0 = b := by rw [← P.center_zero, c.left_inv hb]
  let V := c.target ∩ (φ.surface ∘ c.symm) ⁻¹' c.source
  have hV : IsOpen V := (φ.surface.continuous.comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage c.open_target c.open_source
  have h0V : (0 : ℂ) ∈ V := ⟨hct, by change φ.surface (c.symm 0) ∈ c.source; rwa [hinv0, hfix]⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  have hF : ∀ y ∈ c.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) F y (q.val.toFun y) := P.primitive_derivative
  have hFc : ContinuousAt F b := (hF b hb).mdifferentiableAt.continuousAt
  have hFφ : ContinuousAt (fun y => F (φ.surface y)) b := by
    have hFb : ContinuousAt F (φ.surface b) := by rwa [hfix]
    exact hFb.comp φ.surface.continuous.continuousAt
  have hH : ContinuousAt H b := (toPlane.continuous.continuousAt.comp hFφ).sub
    ((linear A).continuous.continuousAt.comp (toPlane.continuous.continuousAt.comp hFc))
  have hg0 : ContinuousAt g 0 := by
    have hh : ContinuousAt H (c.symm 0) := by rwa [hinv0]
    exact hh.comp (c.symm.continuousAt hct)
  have hlocal : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → ∀ᶠ w in 𝓝 z, g w = g z := by
    intro z hz hz0
    have hzV := hball hz
    have hys : c.symm z ∈ c.source := c.map_target hzV.1
    have hyr : c.symm z ∈ regularSet q := by
      intro hzero
      have heq := P.zero_in_source_eq_center hys hzero
      have hzEq : z = 0 := (c.right_inv hzV.1).symm.trans ((congrArg c heq).trans P.center_zero)
      exact hz0 hzEq
    let y : Regular q := ⟨c.symm z, hyr⟩
    have hyφ : φ.surface y.val ∈ c.source := hzV.2
    have hh := NativeAffinePrimitiveGerms.whole_regular_germ q φ F F c.source c.source c.open_source c.open_source
      hF hF y hys hyφ
    exact (c.symm.continuousAt hzV.1).tendsto hh
  have hconst := PuncturedDiskConstancy.eq_center g hr hg0 hlocal
  have hgzero : g 0 = 0 := by
    dsimp only [g, H]
    rw [hinv0, hfix]
    have hFb : F b = 0 := by dsimp only [F, c]; rw [P.center_zero, zero_pow P.exponent_pos.ne']
    rw [hFb, map_zero, map_zero, sub_self]
  filter_upwards [c.open_source.mem_nhds hb, (c.continuousAt hb).tendsto
    (by simpa only [hc0] using Metric.ball_mem_nhds (0 : ℂ) hr)] with y hyS hyB
  have heq := hconst (c y) hyB
  change H (c.symm (c y)) = g 0 at heq
  rw [c.left_inv hyS, hgzero] at heq
  exact sub_eq_zero.mp heq

end VeechDichotomy.NativeAffinePowerGerms
