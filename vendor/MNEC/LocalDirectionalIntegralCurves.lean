module

public import MNEC.LocalDirectionalCurves
public import MNEC.FlatVectorField
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

@[expose] public section

/-!
# Actual local straight curves are native manifold integral curves

The explicit curves in the physical translation charts satisfy the native
manifold differential equation for the independently constructed intrinsic
directional field. The proof uses the actual inverse-chart derivative and
the chain rule on the explicit affine line. Integrality is proved, not
assumed as a record field. No global completeness or area claim is made.
-/

noncomputable section

namespace MNEC.LocalDirectionalIntegralCurves

open LatticeTorus RegularChartedSpace RegularAtlasCoverage LocalDirectionalCurves Set Topology
open scoped Manifold ContDiff

section ActualManifold

variable {L₁ L₂ : Lattice} {w : Plane}
variable (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)

/-- Native tangent derivative of the explicitly constructed local curve. -/
theorem hasMFDerivAt_curve (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w)
    (t : ℝ) (ht : t ∈ timeDomain hw₁ hw₂ i v x) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) (curve hw₁ hw₂ i v x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) :=
    RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let e := regularChart hw₁ hw₂ i
  let line := fun s : ℝ => e x + s • v
  have hy : line t ∈ (regularChart hw₁ hw₂ i).target := ht
  have hline : HasDerivAt line v t := by
    simpa [line] using!
      ((hasDerivAt_id t).smul_const v).const_add (e x)
  have hlineM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) line t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := hline.hasFDerivAt.hasMFDerivAt
  have hinverse := (FlatChartDerivatives.mdifferentiableAt_regularChart_symm
    hw₁ hw₂ i (line t) hy).hasMFDerivAt
  rw [FlatChartDerivatives.mfderiv_regularChart_symm_id hw₁ hw₂ i (line t) hy] at hinverse
  have hcomp := hinverse.comp t hlineM
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def, curve, line, e] using! hcomp

/-- The actual geometric curve is an integral curve of the actual intrinsic
field on its entire actual valid-time set. -/
theorem isMIntegralCurveOn_curve (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve hw₁ hw₂ i v x) (FlatVectorField.field hw₁ hw₂ v)
      (timeDomain hw₁ hw₂ i v x) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  intro t ht
  rw [FlatVectorField.field_eq_const]
  exact (hasMFDerivAt_curve hw₁ hw₂ i v x t ht).hasMFDerivWithinAt

theorem isMIntegralCurveAt_curve (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w)
    (t : ℝ) (ht : t ∈ timeDomain hw₁ hw₂ i v x) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    IsMIntegralCurveAt (I := 𝓘(ℝ, Plane)) (curve hw₁ hw₂ i v x) (FlatVectorField.field hw₁ hw₂ v) t := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  exact (isMIntegralCurveOn_curve hw₁ hw₂ i v x).isMIntegralCurveAt
    ((timeDomain_open hw₁ hw₂ i v x).mem_nhds ht)

/-- At a point actually in the chosen chart, this native integral curve has
the specified initial value and a genuine open interval of valid times. -/
theorem exists_ball_native_integral_curve (i : Index L₁ L₂ w) (v : Plane)
    (x : Regular L₁ L₂ w) (hx : x ∈ (regularChart hw₁ hw₂ i).source) :
    letI := RegularChartedSpace.chartedSpace hw₁ hw₂
    ∃ ε > 0, Metric.ball (0 : ℝ) ε ⊆ timeDomain hw₁ hw₂ i v x ∧
      curve hw₁ hw₂ i v x 0 = x ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (curve hw₁ hw₂ i v x) (FlatVectorField.field hw₁ hw₂ v)
        (Metric.ball 0 ε) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (timeDomain_open hw₁ hw₂ i v x) 0
    (zero_mem_timeDomain hw₁ hw₂ i v x hx)
  exact ⟨ε, hε, hsub, curve_zero hw₁ hw₂ i v x hx,
    (isMIntegralCurveOn_curve hw₁ hw₂ i v x).mono hsub⟩

end ActualManifold

end MNEC.LocalDirectionalIntegralCurves
