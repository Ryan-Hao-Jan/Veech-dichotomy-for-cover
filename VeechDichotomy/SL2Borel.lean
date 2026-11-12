module

public import VeechDichotomy.LinearGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Metrizable.Basic

/-! The actual SL2 group carries its Borel measurable structure. -/

@[expose] public section

namespace VeechDichotomy.SL2Borel

open LinearGroup

instance measurableSpace : MeasurableSpace SL2 := borel SL2
instance borelSpace : BorelSpace SL2 := ⟨rfl⟩
instance metrizableSpace : TopologicalSpace.MetrizableSpace SL2 := by
  let : TopologicalSpace.MetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.metrizableSpace

end VeechDichotomy.SL2Borel
