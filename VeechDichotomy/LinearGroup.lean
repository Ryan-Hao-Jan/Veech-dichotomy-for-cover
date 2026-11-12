module

public import MNEC.LatticeTorus
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section

namespace VeechDichotomy.LinearGroup

open MNEC.LatticeTorus

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

instance locallyCompactSL2 : LocallyCompactSpace SL2 := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

/-- The usual matrix action on the physical plane. -/
def act (A : SL2) (p : Plane) : Plane :=
  (A.1 0 0 * p.1 + A.1 0 1 * p.2, A.1 1 0 * p.1 + A.1 1 1 * p.2)

end VeechDichotomy.LinearGroup
