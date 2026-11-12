module

public import VeechDichotomy.SL2Borel
public import VeechDichotomy.NativeLatticeQuotient
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Genuine global coordinates SL2(R) = upper-half-plane times its
compact stabilizer at i. The actual continuous section toSL2R supplies
both inverse formulas. Compactness of the stabilizer follows from the
proved proper hyperbolic orbit map, not an assumed Iwasawa decomposition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2HyperbolicCoordinates

open LinearGroup Topology MeasureTheory
open scoped UpperHalfPlane

def isotropy : Subgroup SL2 := MulAction.stabilizer SL2 UpperHalfPlane.I

theorem isCompact_isotropy : IsCompact (isotropy : Set SL2) := by
  change IsCompact ((fun g : SL2 => g • UpperHalfPlane.I) ⁻¹' {UpperHalfPlane.I})
  exact UpperHalfPlane.isProperMap_smul_I.isCompact_preimage isCompact_singleton

instance isotropy_compact : CompactSpace isotropy :=
  isCompact_iff_compactSpace.mp isCompact_isotropy

theorem project_product (z : ℍ) (k : isotropy) :
    (z.toSL2R * (k : SL2)) • UpperHalfPlane.I = z := by
  rw [mul_smul, k.property, UpperHalfPlane.toSL2R_smul_I]

def coordinate (g : SL2) : isotropy := ⟨(g • UpperHalfPlane.I).toSL2R⁻¹ * g, by
  change ((g • UpperHalfPlane.I).toSL2R⁻¹ * g) • UpperHalfPlane.I = UpperHalfPlane.I
  rw [mul_smul, inv_smul_eq_iff, UpperHalfPlane.toSL2R_smul_I]⟩

theorem continuous_coordinate : Continuous coordinate := by
  apply Continuous.subtype_mk
  exact ((UpperHalfPlane.continuous_toSL2R.comp (continuous_id.smul continuous_const)).inv).mul continuous_id

def homeomorph : (ℍ × isotropy) ≃ₜ SL2 where
  toFun p := p.1.toSL2R * (p.2 : SL2)
  invFun g := (g • UpperHalfPlane.I, coordinate g)
  left_inv p := by
    apply Prod.ext
    · exact project_product p.1 p.2
    · apply Subtype.ext
      change ((p.1.toSL2R * (p.2 : SL2)) • UpperHalfPlane.I).toSL2R⁻¹ *
        (p.1.toSL2R * (p.2 : SL2)) = (p.2 : SL2)
      rw [project_product]
      simp
  right_inv g := by
    change (g • UpperHalfPlane.I).toSL2R * ((g • UpperHalfPlane.I).toSL2R⁻¹ * g) = g
    simp
  continuous_toFun := (UpperHalfPlane.continuous_toSL2R.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (continuous_id.smul continuous_const).prodMk continuous_coordinate

def measurableEquiv : (ℍ × isotropy) ≃ᵐ SL2 := homeomorph.toMeasurableEquiv

end VeechDichotomy.SL2HyperbolicCoordinates
