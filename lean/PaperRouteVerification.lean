import Karlin.FaithfulV15
import Lean.Util.CollectAxioms

/-! Reproducible verification of the specified proof routes. This checks dependency
closures, rather than inferring semantic fidelity from a successful build.
The accompanying crosswalk records the manuscript comparison separately. -/
set_option maxHeartbeats 0
set_option pp.fullNames true

open Lean in
run_cmd do
  let env ← getEnv
  let prefixes := #["Karlin.FaithfulPaper", "Karlin.FaithfulEffectiveContract."]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut st : Lean.CollectAxioms.State := {}
  let mut count := 0
  for (name, info) in env.constants.toList do
    if prefixes.any (fun p => name.toString.startsWith p) then
      count := count + 1
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run st
      st := next
      if info.isUnsafe then throwError m!"UNSAFE_ADDITION {name}"
      if let .opaqueInfo _ := info then throwError m!"OPAQUE_ADDITION {name}"
      if let .thmInfo _ := info then logInfo m!"ADDED_THEOREM_TYPE {name}\n{info.type}"
  for ax in st.axioms do
    unless allowed.contains ax do throwError m!"UNEXPECTED_ADDED_AXIOM {ax}"
  for dep in st.visited do
    if dep.toString.startsWith "Karlin." then
      if let some info := env.find? dep then
        if info.isUnsafe then throwError m!"UNSAFE_PROJECT_DEPENDENCY {dep}"
        if let .opaqueInfo _ := info then throwError m!"OPAQUE_PROJECT_DEPENDENCY {dep}"
  logInfo m!"ADDED_CLOSURE_RESULT declarations={count} visited={st.visited.size} axioms={st.axioms.toList}"
  -- The specified route must reach its conclusion independently of the
  -- alternative completeness, summation, and integrality arguments.
  let oldRoutes := #[`Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests,
    `Karlin.FaithfulGrowthRecurrences.bundle_sum_expansion,
    `Karlin.FaithfulGrowthRecurrences.polynomial_height_expansion,
    `Karlin.FaithfulScale.binomial_row_integral_of_values]
  for root in #[`Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff,
      `Karlin.FaithfulPaperAlgebra.clock_bundle_expansion_by_ordinary_powers,
      `Karlin.FaithfulPaperAlgebra.height_expansion_by_degree_drop,
      `Karlin.FaithfulPaperAlgebra.chosenCorrection_forward_difference_formula] do
    let (_, s) := ((Lean.CollectAxioms.collect root).run env).run {}
    for old in oldRoutes do
      if s.visited.contains old then throwError m!"OLD_PROOF_ROUTE_REUSED {root} {old}"
    logInfo m!"INDEPENDENT_ROUTE_RESULT {root} visited={s.visited.size} excluded={oldRoutes}"
  for root in #[`Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem] do
    let (_, s) := ((Lean.CollectAxioms.collect root).run env).run {}
    let mut project := 0
    for ax in s.axioms do
      unless allowed.contains ax do throwError m!"UNEXPECTED_MAIN_AXIOM {root} {ax}"
    for dep in s.visited do
      if dep.toString.startsWith "Karlin." then
        project := project + 1
        if let some info := env.find? dep then
          if info.isUnsafe then throwError m!"UNSAFE_MAIN_DEPENDENCY {dep}"
          if let .opaqueInfo _ := info then throwError m!"OPAQUE_MAIN_DEPENDENCY {dep}"
        for forbidden in #["grounded", "Grounded", "unconditionalRealizedClock",
            "paper_thm_1_1_main", "all_orders_unconditional", "seven_all_integer_time_cubic_gap"] do
          if (dep.toString.splitOn forbidden).length > 1 then
            throwError m!"ALTERNATE_FINAL_WITNESS {dep}"
    logInfo m!"MAIN_CLOSURE_RESULT {root} project={project} total={s.visited.size} axioms={s.axioms.toList}"

#print Karlin.FaithfulEffectiveContract.ThresholdRealizer
#print Karlin.FaithfulEffectiveContract.UniversalThresholdRealizer
#check @Karlin.FaithfulEffectiveContract.lift_every_partrec_parent
#check @Karlin.FaithfulEffectiveContract.lift_every_partrec_parent_program
#check @Karlin.FaithfulEffectiveContract.universal_clock_contract
#check @Karlin.FaithfulMain.main_theorem
#check @Karlin.FaithfulSevenFamily.main_theorem
#check @Karlin.FaithfulPaperCoverage.chosen_strictness
#check @Karlin.FaithfulPaperCoverage.selected_chronology
#check @Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff
#check @Karlin.FaithfulPaperAlgebra.clock_bundle_expansion_by_ordinary_powers
#check @Karlin.FaithfulPaperBounds.clock_phase_boundary_ratios

-- The existing executable witnesses are still ordinary compiled definitions.
def preservedRPSMatrix (k : ℕ) (hk : 2 ≤ k) := Karlin.FaithfulMain.matrix k hk
def preservedSevenMatrix (k : ℕ) (hk : 3 ≤ k) := Karlin.FaithfulSevenFamily.matrix k hk
def preservedRPSThreshold (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) :=
  Karlin.FaithfulEffectiveLift.familyThreshold k hk eps
def preservedSevenThreshold (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) :=
  Karlin.FaithfulSevenFamily.threshold k hk eps
