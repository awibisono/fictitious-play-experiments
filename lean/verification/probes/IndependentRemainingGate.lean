import Karlin.FaithfulV15
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0

namespace IndependentRemaining
open Lean

-- Declaration types are deliberately excluded: merely mentioning a helper's
-- conclusion in an API cannot satisfy these checks.
def valueDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo v) => v.value.getUsedConstants
  | some (.thmInfo v) => v.value.getUsedConstants
  | _ => #[]

def bodyClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut i := 0
  let mut seen : NameSet := {}
  while i < todo.size do
    let n := todo[i]!
    i := i + 1
    if !seen.contains n then
      seen := seen.insert n
      for d in valueDeps env n do
        let owner := match env.getModuleIdxFor? d with
          | some idx => env.header.moduleNames[idx.toNat]!
          | none => Name.anonymous
        if owner.toString.startsWith "Karlin." then todo := todo.push d
  return seen

end IndependentRemaining

open Lean IndependentRemaining in
run_cmd do
  let env ← getEnv
  let routeCases : Array (Name × Array Name × Array Name) := #[
    (`Karlin.FaithfulScale.binomial_row_integral_of_values,
      #[`Karlin.FaithfulFiniteDifference.binomial_row_eq_forward_difference,
        `Karlin.FaithfulFiniteDifference.forward_difference_formula], #[]),
    (`Karlin.FaithfulTables.zeta_leading,
      #[`Karlin.FaithfulPolynomialRoutes.backwardDifference_degree_and_leading,
        `Karlin.FaithfulPolynomialRoutes.backwardDifference_top_coefficient,
        `Karlin.FaithfulPolynomialRoutes.rowPoly_backwardDifference,
        `Karlin.FaithfulPolynomialRoutes.rowPoly_increment_eq],
      #[`Karlin.FaithfulTables.antiderivative_last]),
    (`Karlin.FaithfulInheritance.oldLengthRow_last_pos,
      #[`Karlin.FaithfulPolynomialRoutes.bundle_row_top_coefficient,
        `Karlin.FaithfulPolynomialRoutes.ordinary_power_bundle_expansion,
        `Karlin.FaithfulPolynomialRoutes.polynomial_bundle_remainder,
        `Karlin.FaithfulPolynomialRoutes.bundle_row_eval,
        `Karlin.FaithfulPolynomialRoutes.normalized_limit_of_expansion],
      #[`Karlin.F_tau_mat_diag]),
    (`Karlin.Faithful.actual_reset_signs,
      #[`Karlin.FaithfulAppendix.internal_norm_sum_bound,
        `Karlin.FaithfulAppendix.internal_norm_sum_square_bound,
        `Karlin.Faithful.internal_normStar_bound_with_entry_constants,
        `Karlin.Faithful.score_error_normStar_bound,
        `Karlin.Faithful.interpolation_normStar_scaled_bound,
        `Karlin.Faithful.coupling_error_normStar_bound,
        `Karlin.Faithful.coupling_margins_of_normStar_bound,
        `Karlin.Faithful.cross_positive_of_normStar_bound],
      #[`Karlin.Faithful.coupling_error_bound,
        `Karlin.Faithful.score_error_bound,
        `Karlin.Faithful.internal_linear_bound]),
    (`Karlin.FaithfulRateError.interpolated_polynomial_error,
      #[`Karlin.FaithfulRateError.polynomial_successor_ratio_error,
        `Karlin.FaithfulRateError.within_phase_ratio_error,
        `Karlin.FaithfulRateError.leadingCoeff_pos_of_monotone_phase],
      #[`Karlin.FaithfulRate.interpolated_normalized_limits]),
    (`Karlin.FaithfulRealization.exact_gap_limit,
      #[`Karlin.FaithfulRateError.standard_gap_from_phase_tables_exact_limit,
        `Karlin.FaithfulRateError.standard_gap_from_phase_tables_relative_error,
        `Karlin.FaithfulRateError.normalized_limit_of_relative_error,
        `Karlin.FaithfulRateError.polynomial_successor_ratio_error,
        `Karlin.FaithfulRateError.within_phase_ratio_error],
      #[`Karlin.FaithfulRate.standard_gap_from_phase_tables,
        `Karlin.FaithfulRate.interpolated_normalized_limits]),
    (`Karlin.FaithfulRealization.relative_gap_error,
      #[`Karlin.FaithfulRateError.polynomial_successor_ratio_error,
        `Karlin.FaithfulRateError.within_phase_ratio_error],
      #[`Karlin.FaithfulRate.interpolated_normalized_limits]),
    (`Karlin.FaithfulActualSuffix.actual_suffix,
      #[`Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain,
        `Karlin.FaithfulGatewaySuffix.actual_old_endpoint,
        `Karlin.FaithfulGatewaySuffix.terminal_prefix_gain],
      #[`Karlin.FaithfulLift.nextClock, `Karlin.FaithfulNextClockAssembly.nextRaw]),
    (`Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain,
      #[`Karlin.FaithfulGatewaySuffix.actual_old_endpoint,
        `Karlin.FaithfulGatewaySuffix.terminal_prefix_gain],
      #[`Karlin.FaithfulNextClockAssembly.word_valid,
        `Karlin.FaithfulNextClockAssembly.rotated_end,
        `Karlin.FaithfulActualSuffix.actual_suffix])]
  for (root, required, forbidden) in routeCases do
    unless (env.find? root).isSome do throwError m!"INVALID_ROOT {root}"
    let body := bodyClosure env root
    for n in required do
      unless (env.find? n).isSome do throwError m!"INVALID_AUDIT_NAME {n}"
      unless body.contains n do throwError m!"MISSING_BODY_ROUTE {root} -> {n}"
    for n in forbidden do
      unless (env.find? n).isSome do throwError m!"INVALID_EXCLUSION_NAME {n}"
      if body.contains n then throwError m!"UNEXPECTED_ALTERNATIVE {root} -> {n}"
    logInfo m!"CONSUMER_PASS {root}: required={required.size}; excluded={forbidden.size}; body={body.size}"
  let edges := #[
    (`Karlin.FaithfulScale.binomial_row_integral_of_values,
      `Karlin.FaithfulFiniteDifference.binomial_row_eq_forward_difference),
    (`Karlin.FaithfulTables.zeta_leading,
      `Karlin.FaithfulPolynomialRoutes.backwardDifference_top_coefficient),
    (`Karlin.FaithfulInheritance.oldLengthRow_last_pos,
      `Karlin.FaithfulPolynomialRoutes.bundle_row_top_coefficient),
    (`Karlin.Faithful.actual_reset_signs,
      `Karlin.Faithful.coupling_error_normStar_bound),
    (`Karlin.Faithful.score_error_normStar_bound,
      `Karlin.Faithful.internal_normStar_bound_with_entry_constants),
    (`Karlin.FaithfulRateError.interpolated_polynomial_error,
      `Karlin.FaithfulRateError.within_phase_ratio_error),
    (`Karlin.FaithfulRealization.exact_gap_limit,
      `Karlin.FaithfulRateError.standard_gap_from_phase_tables_exact_limit),
    (`Karlin.FaithfulActualSuffix.actual_suffix,
      `Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain)]
  for (root, dep) in edges do
    unless (valueDeps env root).contains dep do throwError m!"MISSING_DIRECT_EDGE {root} -> {dep}"
    logInfo m!"DIRECT_EDGE_PASS {root} -> {dep}"
  let structural := #[
    `Karlin.FaithfulFiniteDifference.forward_difference_formula,
    `Karlin.FaithfulPolynomialRoutes.ordinary_power_bundle_expansion,
    `Karlin.FaithfulPolynomialRoutes.polynomial_bundle_remainder,
    `Karlin.FaithfulPolynomialRoutes.backwardDifference_degree_and_leading,
    `Karlin.FaithfulAppendix.internal_norm_sum_bound,
    `Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain,
    `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff]
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let roots := #[`Karlin.FaithfulLift.nextClock,
    `Karlin.FaithfulLift.nextAdmissible,
    `Karlin.FaithfulMain.strict_simultaneous,
    `Karlin.FaithfulSevenFamily.strict_simultaneous,
    `Karlin.FaithfulMain.exact_gap,
    `Karlin.FaithfulSevenFamily.exact_gap,
    `Karlin.FaithfulMain.relative_error,
    `Karlin.FaithfulSevenFamily.relative_error,
    `Karlin.FaithfulMain.main_theorem,
    `Karlin.FaithfulSevenFamily.main_theorem]
  for root in roots do
    let body := bodyClosure env root
    for dep in structural do
      unless body.contains dep do throwError m!"MISSING_MAIN_BODY_ROUTE {root} -> {dep}"
    if root != roots[0]! && root != roots[1]! && root != roots[2]! && root != roots[3]! then
      for dep in #[`Karlin.FaithfulRateError.polynomial_successor_ratio_error,
        `Karlin.FaithfulRateError.within_phase_ratio_error] do
        unless body.contains dep do throwError m!"MISSING_MAIN_RATIO_ROUTE {root} -> {dep}"
    let (_, full) := ((Lean.CollectAxioms.collect root).run env).run {}
    for ax in full.axioms do
      unless standard.contains ax do throwError m!"UNEXPECTED_AXIOM {root}: {ax}"
    logInfo m!"MAIN_BODY_PASS {root}: body={body.size}; full={full.visited.size}; axioms={full.axioms.toList}"
