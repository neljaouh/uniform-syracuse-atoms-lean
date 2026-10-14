import PaperProofs
import Lean

/-! Whole-paper completion check for the remaining manuscript.
Every named result and the four additional inputs need an exact
proposition specification and a closed theorem of that type. Missing
specifications are reported, not replaced by axioms or trivial propositions.
Statement-to-manuscript correspondence must still be reviewed mathematically.
No success is reported for a partially formalized manuscript.
Manuscript SHA256: 553ca2aa8dc2a0924ae89590e022c8e61975e2964bc391f82e525f3e6cbd0745
-/

open Lean Elab Command Meta in
run_cmd do
  let required : Array (String × Name × Name) := #[
    ("thm:atoms", `SyracuseReport.MainTheoremA, `SyracuseReport.main_theorem_A),
    ("thm:haar-main", `SyracuseReport.MainTheoremB, `SyracuseReport.main_theorem_B),
    ("thm:density-regularity", `SyracuseReport.DensityRegularityStatement, `SyracuseReport.main_density_regularity),
    ("thm:integrability-main", `SyracuseReport.ExactIntegrabilityStatement, `SyracuseReport.paper_exact_integrability),
    ("prop:energy-upper", `SyracuseReport.CollisionUpperStatement, `SyracuseReport.paper_collision_upper),
    ("cor:offset-integrability", `SyracuseReport.OffsetIntegrabilityStatement, `SyracuseReport.paper_offset_integrability),
    ("thm:predecessors", `SyracuseReport.MainTheoremC, `SyracuseReport.main_theorem_C),
    ("lem:projection", `SyracuseReport.PaperStatements.lem_projection, `SyracuseReport.paper_lem_projection),
    ("lem:error-projection", `SyracuseReport.PaperStatements.lem_error_projection, `SyracuseReport.paper_lem_error_projection),
    ("prop:cylinder", `SyracuseReport.PaperStatements.prop_cylinder, `SyracuseReport.paper_prop_cylinder),
    ("lem:inverse", `SyracuseReport.PaperStatements.lem_inverse, `SyracuseReport.paper_lem_inverse),
    ("prop:criterion-floor", `SyracuseReport.PaperStatements.prop_criterion_floor, `SyracuseReport.paper_prop_criterion_floor),
    ("thm:mixing", `SyracuseReport.PaperStatements.thm_mixing, `SyracuseReport.paper_thm_mixing),
    ("lem:transport", `SyracuseReport.PaperStatements.lem_transport, `SyracuseReport.paper_lem_transport),
    ("lem:block-probability", `SyracuseReport.PaperStatements.lem_block_probability, `SyracuseReport.paper_lem_block_probability),
    ("lem:offset-injective", `SyracuseReport.PaperStatements.lem_offset_injective, `SyracuseReport.paper_lem_offset_injective),
    ("lem:residue-count", `SyracuseReport.PaperStatements.lem_residue_count, `SyracuseReport.paper_lem_residue_count),
    ("lem:kernel-bound", `SyracuseReport.PaperStatements.lem_kernel_bound, `SyracuseReport.paper_lem_kernel_bound),
    ("thm:construction", `SyracuseReport.PaperStatements.thm_construction, `SyracuseReport.paper_thm_construction),
    ("prop:minimum", `SyracuseReport.PaperStatements.prop_minimum, `SyracuseReport.paper_prop_minimum),
    ("lem:stationary", `SyracuseReport.PaperStatements.lem_stationary, `SyracuseReport.paper_lem_stationary),
    ("lem:pure", `SyracuseReport.PaperStatements.lem_pure, `SyracuseReport.paper_lem_pure),
    ("prop:haar", `SyracuseReport.PaperStatements.prop_haar, `SyracuseReport.paper_prop_haar),
    ("thm:counting", `SyracuseReport.PaperStatements.thm_counting, `SyracuseReport.paper_thm_counting),
    ("cor:uniform", `SyracuseReport.PaperStatements.cor_uniform, `SyracuseReport.paper_cor_uniform),
    ("lem:good-roots", `SyracuseReport.PaperStatements.lem_good_roots, `SyracuseReport.paper_lem_good_roots),
    ("lem:seeds", `SyracuseReport.PaperStatements.lem_seeds, `SyracuseReport.paper_lem_seeds),
    ("prop:converse", `SyracuseReport.PaperStatements.prop_converse, `SyracuseReport.paper_prop_converse),
    ("input:admissible-words", `SyracuseReport.PaperStatements.admissible_words, `SyracuseReport.paper_admissible_words),
    ("thm:general-smoothing", `SyracuseReport.GeneralSmoothingStatement, `SyracuseReport.paper_general_smoothing),
    ("prop:finite-cover", `SyracuseReport.FiniteInverseCoverStatement, `SyracuseReport.paper_finite_inverse_cover),
    ("prop:mixing-threshold", `SyracuseReport.PolynomialMixingStatement, `SyracuseReport.paper_polynomial_mixing),
    ("thm:quant-count", `SyracuseReport.QuantitativeCountingStatement, `SyracuseReport.main_quantitative_counting),
    ("lem:prefix-window-sharp", `SyracuseReport.PrefixWindowStatement, `SyracuseReport.paper_prefix_window_sharp),
    ("lem:subpower-families", `SyracuseReport.SubpowerBalancedFamilies, `SyracuseReport.subpower_balanced_families),
    ("lem:word-clock", `SyracuseReport.WordClockStatement, `SyracuseReport.paper_word_clock),
    ("thm:exact-dimension", `SyracuseReport.ExactDimensionStatement, `SyracuseReport.paper_exact_dimension),
    ("thm:dense-spikes", `SyracuseReport.DenseSpikesStatement, `SyracuseReport.paper_dense_spikes),
    ("thm:offset-laws", `SyracuseReport.OffsetLawsStatement, `SyracuseReport.paper_offset_laws),
    ("thm:entropy-obstruction", `SyracuseReport.EntropyObstructionStatement, `SyracuseReport.paper_entropy_obstruction),
    ("cor:geometric-cover", `SyracuseReport.GeometricCoverStatement, `SyracuseReport.paper_geometric_cover),
    ("cor:minus-count", `SyracuseReport.MinusCountingStatement, `SyracuseReport.paper_minus_counting),
    ("input:minus-map", `SyracuseReport.MinusMapStatement, `SyracuseReport.paper_minus_map),
    ("input:integer-offset-unit", `SyracuseReport.IntegerOffsetUnitStatement, `SyracuseReport.paper_integer_offset_unit),
    ("input:offset-conjugacy", `SyracuseReport.OffsetConjugacyStatement, `SyracuseReport.paper_offset_conjugacy),
    ("lem:sqrt-families", `SyracuseReport.SquareRootBalancedFamilies, `SyracuseReport.squareRoot_balanced_families),
    ("thm:sqrt-count", `SyracuseReport.SquareRootCountingStatement, `SyracuseReport.main_sqrtLog_counting)]
  let env ← getEnv
  let mut incomplete := false
  for (label, contract, proof) in required do
    match env.find? contract with
    | none =>
      logError m!"MISSING_STATEMENT|{label}|{contract}"
      incomplete := true
    | some specification =>
      liftTermElabM do
        unless ← isDefEq specification.type (mkSort .zero) do
          throwError "INVALID_SPECIFICATION|{label}|expected a closed proposition"
      match env.find? proof with
      | none =>
        logError m!"MISSING_PROOF|{label}|{proof}|required: {contract}"
        incomplete := true
      | some ci =>
        unless ci matches .thmInfo _ do
          throwError "NOT_A_THEOREM|{label}|{proof}"
        liftTermElabM do
          unless ← isDefEq ci.type (mkConst contract) do
            throwError "WRONG_STATEMENT|{label}|{proof}|expected: {contract}"
        for a in ← collectAxioms proof do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "FORBIDDEN_AXIOM|{label}|{proof}|{a}"
        logInfo m!"RESULT_CHECKED|{label}|{proof}"
  if incomplete then
    logInfo "PAPER_CERTIFICATION_INCOMPLETE|Remaining manuscript not certified"
  else
    logInfo m!"PAPER_ENDPOINTS_CHECKED|{required.size} exact contracts and axiom dependencies checked"
