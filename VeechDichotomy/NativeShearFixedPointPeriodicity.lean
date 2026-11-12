module

public import VeechDichotomy.NativeAffinePowerGerms
public import VeechDichotomy.ComplexSmallPowerFibers
public import VeechDichotomy.NativeShearMatrices
public import VeechDichotomy.FiniteFiberPeriodicity

/-! A genuine native lower-shear affine automorphism fixing any point,
including a zero, has an actual regular periodic point. A sufficiently
small nonzero vertical power-primitive fiber is finite and nonempty;
the whole fiber lies in the affine germ and is invariant under the
actual surface homeomorphism. No foliation or periodic-point oracle is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearFixedPointPeriodicity

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeVeech NativePowerCharts NativeShearMatrices Set Filter Topology Function
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) {a : ℝ} (φ : AffineAutomorphism q (lower a))

theorem exists_regular_periodic (b : X) (hfix : φ.surface b = b) :
    ∃ p : Regular q, ∃ n : ℕ, 0 < n ∧ (φ.regular^[n]) p = p := by
  let P := NativePowerCharts.chosen q b
  let c := P.chart
  have hb : b ∈ c.source := P.center
  have hc0 : c b = 0 := P.center_zero
  have ht0 : (0 : ℂ) ∈ c.target := by simpa only [hc0] using c.map_source hb
  have hinv0 : c.symm 0 = b := by rw [← hc0, c.left_inv hb]
  have hsrc : ∀ᶠ y in 𝓝 b, φ.surface y ∈ c.source :=
    φ.surface.continuous.continuousAt (by simpa only [hfix] using c.open_source.mem_nhds hb)
  have hgerm := NativeAffinePowerGerms.fixed_point_germ q φ b P hfix
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ c.target ∧ φ.surface (c.symm z) ∈ c.source ∧
      toPlane (c (φ.surface (c.symm z)) ^ P.exponent) =
        linear (lower a) (toPlane (c (c.symm z) ^ P.exponent)) := by
    have hinv : Tendsto c.symm (𝓝 0) (𝓝 b) := by
      simpa only [hinv0] using (c.symm.continuousAt ht0).tendsto
    filter_upwards [c.open_target.mem_nhds ht0, hinv hsrc, hinv hgerm] with z hz hzs hzg
    exact ⟨hz, hzs, hzg⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨ε, hε, ⟨z₀, hz₀⟩, hsmall⟩ := ComplexSmallPowerFibers.small_vertical_fiber P.exponent_pos hr
  let w : ℂ := (ε : ℂ) * Complex.I
  have hw : w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hε.ne') Complex.I_ne_zero
  have hvertical : linear (lower a) (toPlane w) = toPlane w := by
    rw [linear_action]
    change (((ε : ℂ) * Complex.I).re, a * ((ε : ℂ) * Complex.I).re +
      ((ε : ℂ) * Complex.I).im) = (((ε : ℂ) * Complex.I).re, ((ε : ℂ) * Complex.I).im)
    simp
  let S : Set X := {y | y ∈ c.source ∧ c y ^ P.exponent = w}
  have hS : S.Finite := Set.Finite.of_injOn
    (fun _ hy => hy.2) (c.injOn.mono fun _ hy => hy.1)
    (ComplexSmallPowerFibers.finite_fiber P.exponent_pos w)
  have hzT : z₀ ∈ c.target := (hball (hsmall z₀ hz₀)).1
  have hy₀ : c.symm z₀ ∈ S := ⟨c.map_target hzT, by rw [c.right_inv hzT]; exact hz₀⟩
  have hmaps : MapsTo φ.surface S S := by
    intro y hy
    have h := hball (hsmall (c y) hy.2)
    change c y ∈ c.target ∧ φ.surface (c.symm (c y)) ∈ c.source ∧
      toPlane (c (φ.surface (c.symm (c y))) ^ P.exponent) =
        linear (lower a) (toPlane (c (c.symm (c y)) ^ P.exponent)) at h
    rw [c.left_inv hy.1] at h
    refine ⟨h.2.1, toPlane.injective ?_⟩
    exact h.2.2.trans ((congrArg (linear (lower a)) (congrArg toPlane hy.2)).trans hvertical)
  have hregular : ∀ y ∈ S, y ∈ regularSet q := by
    intro y hy hzero
    have hyb := P.zero_in_source_eq_center hy.1 hzero
    have hw0 : w = 0 := by
      rw [← hy.2, hyb, hc0, zero_pow P.exponent_pos.ne']
    exact hw hw0
  let : Finite S := hS.to_subtype
  let f : S → S := fun y => ⟨φ.surface y, hmaps y.property⟩
  have hf : Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact φ.surface.injective (congrArg Subtype.val hyz)
  have hval : Semiconj (Subtype.val : S → X) f φ.surface := fun _ => rfl
  obtain ⟨n, hn, hperiod⟩ := hf.mem_periodicPts (⟨c.symm z₀, hy₀⟩ : S)
  have hwhole : (φ.surface^[n]) (c.symm z₀) = c.symm z₀ := hperiod.map hval
  let p : Regular q := ⟨c.symm z₀, hregular _ hy₀⟩
  refine ⟨p, n, hn, Subtype.ext ?_⟩
  have hregularVal : Semiconj (Subtype.val : Regular q → X) φ.regular φ.surface := φ.value
  exact ((hregularVal.iterate_right n) p).trans hwhole

end VeechDichotomy.NativeShearFixedPointPeriodicity
