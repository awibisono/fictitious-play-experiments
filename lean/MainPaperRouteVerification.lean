import Karlin.FaithfulV15
import Lean.Util.CollectAxioms

/-! Dependency verification for the main theorem assembly.
The theorem closures must use the nilpotent/exponential completeness proof
and must exclude the old binomial completeness route. Presence is checked at
each real construction stage, not inserted by an unused final-proof premise.
Raw Clock is still paired explicitly with its positive-rational realizer. -/
set_option maxHeartbeats 0
set_option pp.fullNames true

namespace MainPaperRouteAudit
open Lean

def directDependencies (env : Environment) (name : Name) : Array Name :=
  match env.checked.get.find? name with
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some info => info.type.getUsedConstants
  | none => #[]

/-- A shortest project-declaration path, for human inspection of the assembly. -/
def pathTo (env : Environment) (source target : Name) : Option (Array Name) := Id.run do
  let mut queue := #[#[source]]
  let mut cursor := 0
  let mut seen : NameSet := ({} : NameSet).insert source
  while cursor < queue.size do
    let path := queue[cursor]!
    cursor := cursor + 1
    let current := path.back!
    if current == target then return some path
    for dep in directDependencies env current do
      if dep.toString.startsWith "Karlin." && !seen.contains dep then
        seen := seen.insert dep
        queue := queue.push (path.push dep)
  return none

end MainPaperRouteAudit

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let required := #[
    `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff,
    `Karlin.FaithfulPaperCokernel.D_pow_zero,
    `Karlin.FaithfulPaperCokernel.exp_D_apply,
    `Karlin.FaithfulPaperCokernel.one_sub_exp_neg,
    `Karlin.FaithfulPaperCokernel.expFactor_geometric_inverse,
    `Karlin.FaithfulPaperCokernel.conjugate_adjoint,
    `Karlin.FaithfulPaperCokernel.symmetric_derivation_expansion,
    `Karlin.FaithfulPaperCokernel.paper_binomial_kernel_mem_span]
  let excluded := #[
    `Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests,
    `Karlin.FaithfulCokernel.adjoint_kernel_eq_testSpan,
    `Karlin.FaithfulCokernel.dp_adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.dp_adjoint_kernel_eq_testSpan,
    `Karlin.FaithfulCokernel.momentSection_solves,
    `Karlin.FaithfulCokernel.bounded_moment_solution,
    `Karlin.FaithfulCokernel.exists_fixed_bounded_moment_section,
    `Karlin.FaithfulCokernel.binomialKernelBasis,
    `Karlin.FaithfulCokernel.dividedPowerKernelBasis]
  let roots := #[
    `Karlin.FaithfulPaperCokernel.paper_momentSection_solves,
    `Karlin.FaithfulGain.eventually_gain_and_bounded_correction,
    `Karlin.FaithfulGain.correctedMoment_spec,
    `Karlin.FaithfulGain.AdmissibleGain.momentTable_solves,
    `Karlin.FaithfulGain.AdmissibleGain.eventually_momentTable,
    `Karlin.FaithfulLift.nextClock,
    `Karlin.FaithfulLift.nextAdmissible,
    `Karlin.FaithfulMain.strict_simultaneous,
    `Karlin.FaithfulMain.exact_gap,
    `Karlin.FaithfulSevenFamily.strict_simultaneous,
    `Karlin.FaithfulSevenFamily.exact_gap,
    `Karlin.FaithfulMain.main_theorem,
    `Karlin.FaithfulSevenFamily.main_theorem]
  for root in roots do
    let (_, s) := ((Lean.CollectAxioms.collect root).run env).run {}
    for ax in s.axioms do
      unless allowed.contains ax do throwError m!"UNEXPECTED_AXIOM {root}: {ax}"
    for dep in required do
      unless s.visited.contains dep do throwError m!"MISSING_PDF_ROUTE {root}: {dep}"
    for dep in excluded do
      if s.visited.contains dep then throwError m!"OLD_COKERNEL_ROUTE {root}: {dep}"
    let mut project := 0
    for dep in s.visited do
      if dep.toString.startsWith "Karlin." then
        project := project + 1
        if let some info := env.find? dep then
          if info.isUnsafe then throwError m!"UNSAFE_DEPENDENCY {root}: {dep}"
          if let .opaqueInfo _ := info then throwError m!"OPAQUE_DEPENDENCY {root}: {dep}"
        for forbidden in #["grounded", "Grounded", "unconditionalRealizedClock",
            "paper_thm_1_1_main", "all_orders_unconditional", "seven_all_integer_time_cubic_gap"] do
          if (dep.toString.splitOn forbidden).length > 1 then
            throwError m!"ALTERNATE_FINAL_WITNESS {root}: {dep}"
    logInfo m!"ASSEMBLY_ROUTE_PASS {root}: project={project}; total={s.visited.size}; axioms={s.axioms.toList}"
    match MainPaperRouteAudit.pathTo env root `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff with
    | none => throwError m!"NO_PROJECT_ROUTE_PATH {root}"
    | some path => logInfo m!"ROUTE_PATH {String.intercalate " -> " (path.toList.map Name.toString)}"
  logInfo m!"REQUIRED_PDF_ROUTE {required}"
  logInfo m!"EXCLUDED_OLD_COKERNEL_ROUTE {excluded}"

#print Karlin.FaithfulEffectiveContract.UniversalThresholdRealizer
#check @Karlin.FaithfulEffectiveContract.lift_every_partrec_parent_program
#check @Karlin.FaithfulEffectiveContract.universal_rpsFamily_correct
#check @Karlin.FaithfulEffectiveContract.universal_sevenFamily_correct
#check @Karlin.FaithfulMain.main_theorem
#check @Karlin.FaithfulSevenFamily.main_theorem
#print axioms Karlin.FaithfulEffectiveContract.lift_every_partrec_parent_program
#print axioms Karlin.FaithfulEffectiveContract.universal_clock_program
