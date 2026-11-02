import Karlin.FaithfulV15
import Lean.Util.CollectAxioms

/-! Verify actual use of the remaining written proof routes. The positive
checks traverse declaration bodies only, including generated/private helpers.
Trust checks separately traverse both bodies and types. -/
set_option maxHeartbeats 0

namespace RemainingPaperRouteAudit
open Lean

def bodyDependencies (env : Environment) (name : Name) : Array Name :=
  match env.checked.get.find? name with
  | some (.defnInfo v) => v.value.getUsedConstants
  | some (.thmInfo v) => v.value.getUsedConstants
  | some (.opaqueInfo v) => v.value.getUsedConstants
  | _ => #[]

def bodyClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut queue := #[root]
  let mut cursor := 0
  let mut seen : NameSet := {}
  while cursor < queue.size do
    let current := queue[cursor]!
    cursor := cursor + 1
    unless seen.contains current do
      seen := seen.insert current
      queue := queue ++ bodyDependencies env current
  return seen

def owner (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

structure Gate where
  root : Name
  required : Array Name
  excluded : Array Name := #[]

end RemainingPaperRouteAudit

open Lean RemainingPaperRouteAudit in
run_cmd do
  let env ← getEnv
  let finite := #[`Karlin.FaithfulFiniteDifference.binomial_row_eq_forward_difference,
    `Karlin.FaithfulFiniteDifference.forward_difference_formula]
  let bundle := #[`Karlin.FaithfulPolynomialRoutes.bundle_row_top_coefficient,
    `Karlin.FaithfulPolynomialRoutes.polynomial_bundle_expansion,
    `Karlin.FaithfulPolynomialRoutes.polynomial_bundle_remainder,
    `Karlin.FaithfulPolynomialRoutes.ordinary_power_bundle_expansion]
  let height := #[`Karlin.FaithfulPolynomialRoutes.backwardDifference_degree_and_leading,
    `Karlin.FaithfulPolynomialRoutes.backwardDifference_top_coefficient,
    `Karlin.FaithfulTables.zeta_spec]
  let norms := #[`Karlin.FaithfulAppendix.internal_norm_sum_bound,
    `Karlin.FaithfulAppendix.internal_norm_sum_square_bound,
    `Karlin.Faithful.internal_normStar_bound_with_entry_constants,
    `Karlin.Faithful.score_error_normStar_bound,
    `Karlin.Faithful.coupling_error_normStar_bound]
  let oldNorms := #[`Karlin.Faithful.internal_linear_bound,
    `Karlin.Faithful.score_error_bound, `Karlin.Faithful.coupling_error_bound]
  let ratios := #[`Karlin.FaithfulRateError.polynomial_successor_ratio_error,
    `Karlin.FaithfulRateError.within_phase_ratio_error,
    `Karlin.FaithfulRateError.interpolated_polynomial_error]
  let gateway := #[`Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain,
    `Karlin.FaithfulGatewaySuffix.terminal_prefix_gain,
    `Karlin.FaithfulGatewaySuffix.actual_old_endpoint]
  let oldCokernel := #[`Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests,
    `Karlin.FaithfulCokernel.momentSection_solves]
  let mut gates : Array Gate := #[]
  for root in #[`Karlin.FaithfulScale.binomial_row_integral_of_values,
      `Karlin.FaithfulScale.divided_power_to_binomial_integral,
      `Karlin.FaithfulScaleClock.chosenCorrection_DP,
      `Karlin.FaithfulTables.E_integer, `Karlin.FaithfulTables.F_integer] do
    gates := gates.push ⟨root, finite, #[]⟩
  gates := gates.push ⟨`Karlin.FaithfulInheritance.oldLengthRow_last_pos, bundle,
    #[`Karlin.F_tau_mat_diag]⟩
  gates := gates.push ⟨`Karlin.FaithfulTables.zeta_leading, height,
    #[`Karlin.FaithfulTables.antiderivative_last]⟩
  gates := gates.push ⟨`Karlin.Faithful.actual_reset_signs, norms, oldNorms⟩
  gates := gates.push ⟨`Karlin.FaithfulEffectiveParameters.certificate_valid, norms, #[]⟩
  for root in #[`Karlin.FaithfulRateError.all_integer_polynomial_gap_error,
      `Karlin.FaithfulRealization.exact_gap_limit,
      `Karlin.FaithfulRealization.relative_gap_error] do
    gates := gates.push ⟨root, ratios, #[`Karlin.FaithfulRate.interpolated_normalized_limits]⟩
  gates := gates.push ⟨`Karlin.FaithfulActualSuffix.actual_suffix, gateway, #[]⟩
  gates := gates.push ⟨`Karlin.FaithfulGatewaySuffix.actual_pre_gateway_gain,
    #[`Karlin.FaithfulGatewaySuffix.terminal_prefix_gain,
      `Karlin.FaithfulGatewaySuffix.actual_old_endpoint],
    #[`Karlin.FaithfulNextClockAssembly.word_valid,
      `Karlin.FaithfulNextClockAssembly.rotated_end,
      `Karlin.FaithfulActualSuffix.actual_suffix]⟩
  let construction := finite ++ bundle ++ height ++ norms ++ gateway ++
    #[`Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff]
  for root in #[`Karlin.FaithfulMain.strict_simultaneous,
      `Karlin.FaithfulSevenFamily.strict_simultaneous] do
    gates := gates.push ⟨root, construction, oldCokernel⟩
  for root in #[`Karlin.FaithfulMain.exact_gap, `Karlin.FaithfulMain.relative_error,
      `Karlin.FaithfulSevenFamily.exact_gap, `Karlin.FaithfulSevenFamily.relative_error,
      `Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem] do
    gates := gates.push ⟨root, construction ++ ratios, oldCokernel⟩
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for gate in gates do
    unless env.contains gate.root do throwError m!"MISSING_ROOT {gate.root}"
    let bodies := bodyClosure env gate.root
    for required in gate.required do
      unless bodies.contains required do
        throwError m!"MISSING_BODY_ROUTE {gate.root}: {required}"
    let (_, closure) := ((Lean.CollectAxioms.collect gate.root).run env).run {}
    for excluded in gate.excluded do
      if closure.visited.contains excluded then
        throwError m!"ALTERNATE_ROUTE_IN_LOCAL_CLOSURE {gate.root}: {excluded}"
    for ax in closure.axioms do
      unless allowed.contains ax do throwError m!"NONSTANDARD_AXIOM {gate.root}: {ax}"
    logInfo m!"WRITTEN_ROUTE_PASS {gate.root}: bodies={bodies.size}; full={closure.visited.size}; axioms={closure.axioms.toList}; required={gate.required}; excluded={gate.excluded}"

  -- Declaration ownership also includes names generated in private namespaces.
  let mut count := 0
  let mut theoremCount := 0
  let mut moduleCounts : Std.HashMap Name Nat := {}
  let mut union : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let mod := owner env name
    if mod.toString.startsWith "Karlin.Faithful" then
      count := count + 1
      if let .thmInfo _ := info then theoremCount := theoremCount + 1
      moduleCounts := moduleCounts.insert mod (moduleCounts.getD mod 0 + 1)
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run union
      union := next
  for ax in union.axioms do
    unless allowed.contains ax do throwError m!"NONSTANDARD_OWNED_AXIOM {ax}"
  for dep in union.visited do
    if (owner env dep).toString.startsWith "Karlin." then
      if let some info := env.find? dep then
        if info.isUnsafe then throwError m!"UNSAFE_PROJECT_DEPENDENCY {dep}"
        if let .opaqueInfo _ := info then throwError m!"OPAQUE_PROJECT_DEPENDENCY {dep}"
      for forbidden in #["grounded", "Grounded", "unconditionalRealizedClock",
          "paper_thm_1_1_main", "all_orders_unconditional", "seven_all_integer_time_cubic_gap"] do
        if (dep.toString.splitOn forbidden).length > 1 then
          throwError m!"ALTERNATE_FINAL_WITNESS {dep}"
  logInfo m!"OWNED_TRUST_PASS modules={moduleCounts.size}; declarations={count}; theorems={theoremCount}; closure={union.visited.size}; axioms={union.axioms.toList}"
  logInfo m!"WRITTEN_ROUTE_GATES_PASSED {gates.size}"

#print Karlin.FaithfulEffectiveContract.UniversalThresholdRealizer
#check @Karlin.FaithfulEffectiveContract.lift_every_partrec_parent_program
#check @Karlin.FaithfulEffectiveContract.universal_rpsFamily_correct
#check @Karlin.FaithfulEffectiveContract.universal_sevenFamily_correct
#check @Karlin.FaithfulMain.main_theorem
#check @Karlin.FaithfulSevenFamily.main_theorem
