module

public import VeechDichotomy.ComplexDisplacementParameters
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! The actual open complex displacement domain with its inclusion
chart. This is the standard open-subset complex structure. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexDisplacementManifold

open ComplexDisplacementParameters
open scoped Manifold ContDiff

variable (m : ℕ)

instance chartedSpace : ChartedSpace (Space m) (Parameters m) :=
  (chart m).singletonChartedSpace (chart_source m)

instance isComplexManifold (n : ℕ∞ω) : IsManifold 𝓘(ℂ, Space m) n (Parameters m) :=
  (chart m).isManifold_singleton (chart_source m)

end VeechDichotomy.ComplexDisplacementManifold
