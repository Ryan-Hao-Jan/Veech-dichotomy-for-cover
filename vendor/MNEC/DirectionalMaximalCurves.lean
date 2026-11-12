module

public import MNEC.FlatVectorField
public import MNEC.MaximalIntegralCurve
public import MNEC.RegularTopologyArea
public import MNEC.RegularCountability

@[expose] public section

/-!
# Actual maximal directional trajectories on the regular slit surface

The generic native maximal-curve construction is instantiated with the
independently proved smooth physical vector field. Smoothness, Hausdorffness,
boundarylessness and local existence are derived, rather than supplied as
directional-flow fields. Completeness and a conull complete-orbit set remain
separate obligations.
-/

noncomputable section

namespace MNEC.DirectionalMaximalCurves

open LatticeTorus RegularChartedSpace Set
open scoped Manifold ContDiff Topology

section ActualManifold

variable {L₁ L₂ : Lattice} {w : Plane}
variable (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)

theorem field_contMDiff_one (v : Plane) :
    letI := chartedSpace hw₁ hw₂
    letI : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
    ContMDiff 𝓘(ℝ, Plane) (𝓘(ℝ, Plane)).tangent 1
      (fun x : Regular L₁ L₂ w =>
        (⟨x, FlatVectorField.field hw₁ hw₂ v x⟩ : TangentBundle 𝓘(ℝ, Plane) (Regular L₁ L₂ w))) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  exact (FlatVectorField.contMDiff_field hw₁ hw₂ v).of_le (by simp)

def domain (v : Plane) (x : Regular L₁ L₂ w) : Set ℝ := by
  let := chartedSpace hw₁ hw₂
  exact MaximalIntegralCurve.maximalDomain (FlatVectorField.field hw₁ hw₂ v) x

def trajectory (v : Plane) (x : Regular L₁ L₂ w) : ℝ → Regular L₁ L₂ w := by
  let := chartedSpace hw₁ hw₂
  exact MaximalIntegralCurve.maximalCurve (FlatVectorField.field hw₁ hw₂ v) x

theorem domain_open (v : Plane) (x : Regular L₁ L₂ w) : IsOpen (domain hw₁ hw₂ v x) := by
  let := chartedSpace hw₁ hw₂
  exact MaximalIntegralCurve.maximalDomain_open _ _

theorem domain_convex (v : Plane) (x : Regular L₁ L₂ w) : Convex ℝ (domain hw₁ hw₂ v x) := by
  let := chartedSpace hw₁ hw₂
  exact MaximalIntegralCurve.maximalDomain_convex _ _

theorem domain_ordConnected (v : Plane) (x : Regular L₁ L₂ w) : OrdConnected (domain hw₁ hw₂ v x) := by
  let := chartedSpace hw₁ hw₂
  exact MaximalIntegralCurve.maximalDomain_ordConnected _ _

theorem zero_mem_domain (v : Plane) (x : Regular L₁ L₂ w) : 0 ∈ domain hw₁ hw₂ v x := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  exact MaximalIntegralCurve.zero_mem_maximalDomain (x₀ := x) (field_contMDiff_one hw₁ hw₂ v)

theorem trajectory_initial (v : Plane) (x : Regular L₁ L₂ w) : trajectory hw₁ hw₂ v x 0 = x := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalIntegralCurve.maximalCurve_initial (x₀ := x) (field_contMDiff_one hw₁ hw₂ v)

theorem trajectory_isMIntegralCurveOn (v : Plane) (x : Regular L₁ L₂ w) :
    letI := chartedSpace hw₁ hw₂
    IsMIntegralCurveOn (trajectory hw₁ hw₂ v x) (FlatVectorField.field hw₁ hw₂ v)
      (domain hw₁ hw₂ v x) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  exact MaximalIntegralCurve.maximalCurve_isMIntegralCurveOn (x₀ := x) (field_contMDiff_one hw₁ hw₂ v)

theorem domain_connected (v : Plane) (x : Regular L₁ L₂ w) : IsConnected (domain hw₁ hw₂ v x) := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  exact MaximalIntegralCurve.maximalDomain_connected (x₀ := x) (field_contMDiff_one hw₁ hw₂ v)

theorem extends_every_open_interval (v : Plane) (x : Regular L₁ L₂ w)
    (U : Set ℝ) (γ : ℝ → Regular L₁ L₂ w) (hU : IsOpen U) (hord : OrdConnected U)
    (hzero : 0 ∈ U) (hγzero : γ 0 = x) :
    letI := chartedSpace hw₁ hw₂
    IsMIntegralCurveOn γ (FlatVectorField.field hw₁ hw₂ v) U →
      U ⊆ domain hw₁ hw₂ v x ∧ EqOn (trajectory hw₁ hw₂ v x) γ U := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  intro hγ
  exact MaximalIntegralCurve.extends_every_open_interval (field_contMDiff_one hw₁ hw₂ v)
    U γ hU hord hzero hγzero hγ

theorem no_proper_open_interval_extension (v : Plane) (x : Regular L₁ L₂ w)
    (U : Set ℝ) (γ : ℝ → Regular L₁ L₂ w) (hU : IsOpen U) (hord : OrdConnected U)
    (hzero : 0 ∈ U) (hγzero : γ 0 = x) :
    letI := chartedSpace hw₁ hw₂
    IsMIntegralCurveOn γ (FlatVectorField.field hw₁ hw₂ v) U →
      domain hw₁ hw₂ v x ⊆ U →
        U = domain hw₁ hw₂ v x ∧ EqOn (trajectory hw₁ hw₂ v x) γ U := by
  let := chartedSpace hw₁ hw₂
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular L₁ L₂ w) := RegularSmoothStructure.isManifold_smooth hw₁ hw₂
  let : T2Space (Regular L₁ L₂ w) := RegularTopologyArea.regularT2Space L₁ L₂ w hw₁ hw₂
  intro hγ hcontains
  exact MaximalIntegralCurve.no_proper_open_interval_extension (field_contMDiff_one hw₁ hw₂ v)
    U γ hU hord hzero hγzero hγ hcontains

end ActualManifold

end MNEC.DirectionalMaximalCurves
