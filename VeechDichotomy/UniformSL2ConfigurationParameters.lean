module

public import VeechDichotomy.ConvergentBeltramiConfigurationParameters
public import VeechDichotomy.BeltramiMarkedScaledFamily
public import VeechDichotomy.NativeSL2AnalyticFamily

/-! Concrete simultaneous family parameters formed from the GIVEN SL2
matrix and actual branch tuple. Their base differential is exactly the
native analytic realization of that matrix, with no dependent chart choice. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformSL2ConfigurationParameters

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane LinearGroup Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

def markParameters (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) :
    ComplexBeltramiMarkParameters.Parameters A := parameters A (SL2BeltramiParameters.parameter L) u h

def familyParameters (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) :
    BeltramiMarkedScaledFamily.Base A := ((NativeSL2AnalyticFamily.parameters L).1, markParameters A L u h)

theorem native_parameter (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) :
    BeltramiMarkedReferenceCharts.parameter A (markParameters A L u h) = SL2BeltramiParameters.parameter L := rfl

local instance (L : SL2) : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface q L) := WholeDeformedAtlas.chartedSpace q L
local instance (L : SL2) : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface q L) := WholeDeformedAtlas.isComplexManifold q L ω

def baseEquivalence (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) :
    MNEC.NativeDifferentialEquiv.Equiv (WholeDeformedDifferential.form q L)
      (BeltramiMarkedScaledFamily.baseFiberForm (familyParameters A L u h)) :=
  NativeSL2AnalyticFamily.equivalence q L

theorem baseEquivalence_point (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u)
    (x : WholeDeformedAtlas.WholeSurface q L) : ((baseEquivalence A L u h).homeomorph x).point = x.point := rfl

def transport (F : Family A) (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) :
    NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L) ≃ₜ
      NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L) :=
  F.nativeMap (ComplexBeltramiMarkParameters.productHomeomorph A (markParameters A L u h))

theorem transport_moves (F : Family A) (L : SL2) (u : Fin m → X) (h : Valid A (SL2BeltramiParameters.parameter L) u) (i : Fin m) :
    transport A F L u h ⟨b i⟩ = (⟨u i⟩ : NativeBeltramiSurface.Surface q (SL2BeltramiParameters.parameter L)) := by
  apply (NativeBeltramiSurface.toOriginal q (SL2BeltramiParameters.parameter L)).injective
  exact congrFun (parameters_moves A F (SL2BeltramiParameters.parameter L) u h) i

end VeechDichotomy.UniformSL2ConfigurationParameters
