import Karlin.FaithfulV15
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0

namespace IndependentAssembly
open Lean

-- Traverse proof/definition VALUES only, not declaration types. Also record
-- direct edges so actual source assembly can be checked independently.
def valueDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo v) => v.value.getUsedConstants
  | some (.thmInfo v) => v.value.getUsedConstants
  | _ => #[]

def bodyProjectClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut i := 0
  let mut seen : NameSet := {}
  while i < todo.size do
    let n := todo[i]!
    i := i+1
    if !seen.contains n then
      seen := seen.insert n
      for d in valueDeps env n do
        let owner := match env.getModuleIdxFor? d with
          | some idx => env.header.moduleNames[idx.toNat]!
          | none => Name.anonymous
        if owner.toString.startsWith "Karlin." then todo := todo.push d
  return seen

end IndependentAssembly

open Lean IndependentAssembly in
run_cmd do
  let env ← getEnv
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let required := #[`Karlin.FaithfulPaperCokernel.paper_momentSection_solves,
    `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff,
    `Karlin.FaithfulPaperCokernel.D_pow_zero,
    `Karlin.FaithfulPaperCokernel.exp_D_apply,
    `Karlin.FaithfulPaperCokernel.one_sub_exp_neg,
    `Karlin.FaithfulPaperCokernel.expFactor_geometric_inverse,
    `Karlin.FaithfulPaperCokernel.conjugate_adjoint,
    `Karlin.FaithfulPaperCokernel.symmetric_derivation_expansion,
    `Karlin.FaithfulPaperCokernel.paper_binomial_kernel_mem_span]
  let excluded := #[`Karlin.FaithfulCokernel.momentSection_solves,
    `Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests,
    `Karlin.FaithfulCokernel.adjoint_kernel_eq_testSpan,
    `Karlin.FaithfulCokernel.dp_adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.dp_adjoint_kernel_eq_testSpan,
    `Karlin.FaithfulCokernel.bounded_moment_solution,
    `Karlin.FaithfulCokernel.exists_fixed_bounded_moment_section,
    `Karlin.FaithfulCokernel.binomialKernelBasis,
    `Karlin.FaithfulCokernel.dividedPowerKernelBasis]
  let roots := #[`Karlin.FaithfulPaperCokernel.paper_momentSection_solves,
    `Karlin.FaithfulGain.eventually_gain_and_bounded_correction,
    `Karlin.FaithfulGain.correctedMoment_spec,
    `Karlin.FaithfulGain.AdmissibleGain.momentTable_solves,
    `Karlin.FaithfulGain.AdmissibleGain.eventually_momentTable,
    `Karlin.FaithfulLift.nextClock, `Karlin.FaithfulLift.nextAdmissible,
    `Karlin.FaithfulMain.strict_simultaneous, `Karlin.FaithfulMain.exact_gap,
    `Karlin.FaithfulSevenFamily.strict_simultaneous, `Karlin.FaithfulSevenFamily.exact_gap,
    `Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem]
  for root in roots do
    let body := bodyProjectClosure env root
    let (_, full) := ((Lean.CollectAxioms.collect root).run env).run {}
    for ax in full.axioms do
      unless standard.contains ax do throwError m!"UNEXPECTED_AXIOM {root}: {ax}"
    for dep in required do
      unless body.contains dep do throwError m!"MISSING_BODY_ROUTE {root}: {dep}"
    for dep in excluded do
      if full.visited.contains dep then throwError m!"OLD_ROUTE {root}: {dep}"
    logInfo m!"INDEPENDENT_BODY_ROUTE_PASS {root}: bodyProject={body.size}; full={full.visited.size}; axioms={full.axioms.toList}"
  let edges := #[
    (`Karlin.FaithfulGain.eventually_gain_and_bounded_correction,
      `Karlin.FaithfulPaperCokernel.paper_momentSection_solves),
    (`Karlin.FaithfulGain.correctedMoment_spec,
      `Karlin.FaithfulPaperCokernel.paper_momentSection_solves),
    (`Karlin.FaithfulPaperCokernel.paper_momentSection_solves,
      `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff),
    (`Karlin.FaithfulPaperCokernel.paper_momentSection_solves,
      `Karlin.FaithfulEffectiveLinear.section_on_range)]
  for (a,b) in edges do
    unless (valueDeps env a).contains b do throwError m!"MISSING_DIRECT_EDGE {a} -> {b}"
    logInfo m!"DIRECT_PROOF_EDGE {a} -> {b}"
  for root in #[`Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem] do
    let (_, full) := ((Lean.CollectAxioms.collect root).run env).run {}
    for dep in #[`Karlin.FaithfulGrowthRecurrences.bundle_sum_expansion,
      `Karlin.FaithfulGrowthRecurrences.polynomial_height_expansion,
      `Karlin.FaithfulScale.binomial_row_integral_of_values,
      `Karlin.FaithfulPaperAlgebra.clock_bundle_expansion_by_ordinary_powers,
      `Karlin.FaithfulPaperAlgebra.height_expansion_by_degree_drop,
      `Karlin.FaithfulPaperAlgebra.chosenCorrection_forward_difference_formula,
      `Karlin.FaithfulPaperBounds.internal_norm_sum_bound,
      `Karlin.FaithfulPaperChronology.pre_gateway_gain] do
      logInfo m!"OTHER_ROUTE {root}: {dep}={full.visited.contains dep}"
    for dep in #[`Karlin.FaithfulTables.zeta_leading,
      `Karlin.FaithfulInheritance.oldLengthRow_last_pos,
      `Karlin.FaithfulRate.binomial_Ico_sum,
      `Karlin.FaithfulRate.interpolated_normalized_limits,
      `Karlin.FaithfulRateError.interpolated_polynomial_error,
      `Karlin.FaithfulRateError.standard_gap_from_phase_tables_relative_error,
      `Karlin.FaithfulPaperBounds.clock_phase_boundary_ratios,
      `Karlin.FaithfulAppendix.linear_internal_bound,
      `Karlin.Faithful.internal_linear_bound,
      `Karlin.Faithful.score_error_bound,
      `Karlin.FaithfulInheritance.rotated_suffix,
      `Karlin.FaithfulPaperChronology.actual_future_reset_deficit,
      `Karlin.FaithfulPaperChronology.actual_earlier_reset_deficit] do
      unless (env.find? dep).isSome do throwError m!"INVALID_AUDIT_NAME {dep}"
      logInfo m!"ACTUAL_ROUTE {root}: {dep}={full.visited.contains dep}"
    for mod in #[`Karlin.FaithfulPaperAlgebra, `Karlin.FaithfulPaperBounds,
      `Karlin.FaithfulPaperChronology, `Karlin.FaithfulPaperCoverage,
      `Karlin.FaithfulPaperSeeds, `Karlin.FaithfulPaperCokernel,
      `Karlin.FaithfulEffectiveContract] do
      let mut n := 0
      for dep in full.visited do
        if let some idx := env.getModuleIdxFor? dep then
          if env.header.moduleNames[idx.toNat]! == mod then n := n+1
      logInfo m!"COMPANION_MODULE_USE {root}: {mod}={n}"

-- New theorem covers exactly the old specification including k=0, and the
-- kernel verifies the two proof terms inhabit precisely the same proposition.
example : @Karlin.FaithfulPaperCokernel.paper_momentSection_solves =
    @Karlin.FaithfulCokernel.momentSection_solves := rfl
