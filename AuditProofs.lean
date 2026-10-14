import PaperProofs
import Lean

/-! Axiom audit of the implemented paper namespace. This complements the
exact endpoint checks; it is not a replacement for CheckPaper's coverage gate.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  for (name, ci) in env.constants.toList do
    if (`SyracuseReport).isPrefixOf name then
      for a in ← collectAxioms name do
        unless allowed.contains a do
          throwError "FORBIDDEN_AXIOM|{name}|{a}"
      declarations := declarations + 1
      if ci matches .thmInfo _ then
        theorems := theorems + 1
  logInfo m!"PAPER_NAMESPACE_CHECKED|{declarations}|{theorems}|{allowed.toList}"
