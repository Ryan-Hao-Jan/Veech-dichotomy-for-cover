module

import VeechDichotomy
import Lean

open Lean Elab Command

/-! Reject any project declaration with a transitive dependency on a
nonstandard axiom, including `sorryAx` and native-evaluation trust axioms.
The exact main proof must be present; its type is independently
rechecked against the paper statement in CheckMainTheorem.lean.
-/

run_cmd do
  let env ← getEnv
  if (env.find? `VeechDichotomy.PaperMainTheorem.main).isNone then
    throwError "The exact main theorem proof was not loaded."
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if #[`VeechDichotomy, `MNEC, `Jacobians].any (·.isPrefixOf name)
      then some name else none).toArray
  if names.isEmpty then
    throwError "No project declarations were loaded."
  let names := names.qsort Name.quickLt
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
  logInfo m!"AXIOM_AUDIT_PASSED: {names.size} project declarations; only standard Lean foundations."
  logInfo "EXACT_MAIN_THEOREM_AUDITED: VeechDichotomy.PaperMainTheorem.main"
