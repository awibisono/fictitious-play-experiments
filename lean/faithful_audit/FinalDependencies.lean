import Karlin.FaithfulMain
import Karlin.FaithfulRPS
import Karlin.FaithfulScaleClock
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #["groundedBundleTower", "GroundedClockBundle",
    "unconditionalRealizedClock", "all_orders_unconditional_karlin_theorem",
    "unconditional_karlin_theorem", "paper_thm_1_1_main",
    "grounded", "Grounded", "all_orders", "unconditional", "RealizedClock"]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut state : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn "Karlin.Faithful").length > 1 then
      count := count + 1
      if let .thmInfo _ := info then theoremCount := theoremCount + 1
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
      state := next
  for ax in state.axioms do
    unless permitted.contains ax do throwError m!"DISALLOWED AXIOM {ax}"
  for dep in state.visited do
    for term in forbidden do
      if (dep.toString.splitOn "Karlin.").length > 1 &&
          (dep.toString.splitOn term).length > 1 then
        throwError m!"FORBIDDEN DEPENDENCY {dep}"
  logInfo m!"FINAL_ALL_FAITHFUL_AUDIT declarations={count} theorems={theoremCount} axioms={state.axioms.toList} no_grounded_or_old_main=true"
  let (_, mainState) := ((Lean.CollectAxioms.collect `Karlin.FaithfulMain.main_theorem).run env).run {}
  let mut faithfulDeps : Nat := 0
  for dep in mainState.visited do
    if (dep.toString.splitOn "Karlin.Faithful").length > 1 then faithfulDeps := faithfulDeps + 1
  logInfo m!"FINAL_MAIN_CLOSURE faithful_dependencies={faithfulDeps} axioms={mainState.axioms.toList}"
  for dep in mainState.visited do
    if dep.toString.startsWith "Karlin." && !dep.toString.startsWith "Karlin.Faithful" then
      logInfo m!"GENERIC_KARLIN_DEPENDENCY {dep}"

#print Karlin.FaithfulMain.main_theorem
#print axioms Karlin.FaithfulMain.main_theorem
#print axioms Karlin.FaithfulLift.nextClock
#print axioms Karlin.FaithfulLift.nextAdmissible
#print axioms Karlin.FaithfulMain.constant_formula
#print axioms Karlin.FaithfulMain.empiricalStrategy_eq_counts
