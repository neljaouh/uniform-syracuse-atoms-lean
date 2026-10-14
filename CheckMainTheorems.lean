import PaperProofs
import Lean

/-! Completion check for the exact main-theorem statements.
This checks the atom, density, exact integrability, counting, general smoothing, geometry and
offset endpoints, including both quantitative counting and clock theorems.
This checks the main conclusions; it is not a coverage check for every
intermediate lemma and published input in the manuscript.
-/

open Lean Elab Command Meta in
run_cmd do
  let required := #[
    (`SyracuseReport.main_theorem_A, `SyracuseReport.MainTheoremA),
    (`SyracuseReport.main_theorem_B, `SyracuseReport.MainTheoremB),
    (`SyracuseReport.main_density_regularity, `SyracuseReport.DensityRegularityStatement),
    (`SyracuseReport.paper_exact_integrability, `SyracuseReport.ExactIntegrabilityStatement),
    (`SyracuseReport.paper_collision_upper, `SyracuseReport.CollisionUpperStatement),
    (`SyracuseReport.paper_offset_integrability, `SyracuseReport.OffsetIntegrabilityStatement),
    (`SyracuseReport.main_theorem_C, `SyracuseReport.MainTheoremC),
    (`SyracuseReport.paper_general_smoothing, `SyracuseReport.GeneralSmoothingStatement),
    (`SyracuseReport.main_quantitative_counting, `SyracuseReport.QuantitativeCountingStatement),
    (`SyracuseReport.paper_exact_dimension, `SyracuseReport.ExactDimensionStatement),
    (`SyracuseReport.paper_dense_spikes, `SyracuseReport.DenseSpikesStatement),
    (`SyracuseReport.paper_offset_laws, `SyracuseReport.OffsetLawsStatement),
    (`SyracuseReport.main_sqrtLog_counting, `SyracuseReport.SquareRootCountingStatement)]
  let env ← getEnv
  let mut missing := false
  for (name, contract) in required do
    match env.find? name with
    | none =>
      logError m!"MISSING_PROOF|{name}|required closed type: {contract}"
      missing := true
    | some ci =>
      unless ci matches .thmInfo _ do
        throwError "{name} must be a theorem, not a definition or axiom"
      liftTermElabM do
        unless ← isDefEq ci.type (mkConst contract) do
          throwError "WRONG_STATEMENT|{name}|expected {contract}, got {ci.type}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "FORBIDDEN_AXIOM|{name}|{a}"
      logInfo m!"ENDPOINT_OK|{name}|{axioms}"
  if missing then
    logInfo "MAIN_THEOREMS_INCOMPLETE|The expanded headline results are not certified"
  else
    logInfo "MAIN_THEOREMS_OK|All exact endpoints and axioms checked"
