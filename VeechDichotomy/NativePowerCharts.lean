module

public import VeechDichotomy.NativeZeroCoordinates

/-! Chosen genuine holomorphic power charts, with proved zero isolation.
Existence is discharged by the native primitive/power-coordinate theorem;
the structure does not postulate a missing local normal-form theorem.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativePowerCharts

open MNEC.NativeAbelianDifferential Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure PowerChart (q : Differential X) (b : X) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  chart : OpenPartialHomeomorph X ℂ
  center : b ∈ chart.source
  center_zero : chart b = 0
  primitive_derivative : ∀ y ∈ chart.source,
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z : X => (chart z) ^ exponent) y (q.val.toFun y)
  holomorphic : ∀ y ∈ chart.source, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω chart y
  inverse_holomorphic : ∀ z ∈ chart.target, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω chart.symm z

theorem exists_powerChart (q : Differential X) (b : X) : Nonempty (PowerChart q b) := by
  obtain ⟨k, hk, e, hb, he0, hder, he, hinv⟩ := NativeZeroCoordinates.exists_native_power_chart q b
  exact ⟨⟨k, hk, e, hb, he0, hder, he, hinv⟩⟩

def chosen (q : Differential X) (b : X) : PowerChart q b :=
  Classical.choice (exists_powerChart q b)

namespace PowerChart

variable {q : Differential X} {b : X}

theorem mdifferentiable (p : PowerChart q b) : p.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  ⟨fun y hy => (p.holomorphic y hy).mdifferentiableAt (by decide) |>.mdifferentiableWithinAt,
    fun z hz => (p.inverse_holomorphic z hz).mdifferentiableAt (by decide) |>.mdifferentiableWithinAt⟩

theorem chart_derivative_ne_zero (p : PowerChart q b) {y : X} (hy : y ∈ p.chart.source) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) p.chart y ≠ 0 := by
  intro hzero
  let : Nontrivial (TangentSpace 𝓘(ℂ) y) := inferInstanceAs (Nontrivial ℂ)
  have hinj := (p.mdifferentiable.mfderiv hy).injective
  change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) p.chart y) at hinj
  rw [hzero] at hinj
  exact Function.not_injective_const hinj

theorem form_derivative_formula (p : PowerChart q b) {y : X} (hy : y ∈ p.chart.source) :
    q.val.toFun y = ((p.exponent : ℂ) * p.chart y ^ (p.exponent - 1)) •
      mfderiv 𝓘(ℂ) 𝓘(ℂ) p.chart y := by
  have hp : HasDerivAt (fun z : ℂ => z ^ p.exponent)
      ((p.exponent : ℂ) * p.chart y ^ (p.exponent - 1)) (p.chart y) := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id (p.chart y)).pow p.exponent
  have hpf : HasFDerivAt (fun z : ℂ => z ^ p.exponent)
      (((p.exponent : ℂ) * p.chart y ^ (p.exponent - 1)) • ContinuousLinearMap.id ℂ ℂ)
      (p.chart y) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hp
  have hc := hpf.hasMFDerivAt.comp y (p.mdifferentiable.mdifferentiableAt hy).hasMFDerivAt
  have h := (HasMFDerivAt.mfderiv (p.primitive_derivative y hy)).symm.trans hc.mfderiv
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using! h

theorem zero_in_source_eq_center (p : PowerChart q b) {y : X}
    (hy : y ∈ p.chart.source) (hq : y ∈ zeroSet q) : y = b := by
  have hzero : ((p.exponent : ℂ) * p.chart y ^ (p.exponent - 1)) •
      mfderiv 𝓘(ℂ) 𝓘(ℂ) p.chart y = 0 := (p.form_derivative_formula hy).symm.trans hq
  have hs := (smul_eq_zero.mp hzero).resolve_right (p.chart_derivative_ne_zero hy)
  have hn : (p.exponent : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.exponent_pos.ne'
  have hp0 : p.chart y ^ (p.exponent - 1) = 0 := (mul_eq_zero.mp hs).resolve_left hn
  have he0 : p.chart y = 0 := eq_zero_of_pow_eq_zero hp0
  exact p.chart.injOn hy p.center (he0.trans p.center_zero.symm)

theorem zero_at_center_iff_one_lt (p : PowerChart q b) :
    b ∈ zeroSet q ↔ 1 < p.exponent := by
  constructor
  · intro hq
    have hk : p.exponent ≠ 1 := by
      intro hk1
      have h := p.form_derivative_formula p.center
      simp only [hk1, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, one_smul] at h
      exact p.chart_derivative_ne_zero p.center (h.symm.trans hq)
    exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr p.exponent_pos.ne') hk.symm
  · intro hk
    change q.val.toFun b = 0
    rw [p.form_derivative_formula p.center, p.center_zero,
      zero_pow (Nat.sub_ne_zero_of_lt hk), mul_zero, zero_smul]

theorem regular_center_exponent_one (p : PowerChart q b) (hb : b ∈ regularSet q) :
    p.exponent = 1 := by
  have hnot : ¬ 1 < p.exponent := fun hk => hb (p.zero_at_center_iff_one_lt.mpr hk)
  exact Nat.le_antisymm (Nat.le_of_not_gt hnot) (Nat.one_le_iff_ne_zero.mpr p.exponent_pos.ne')

end PowerChart
end VeechDichotomy.NativePowerCharts
