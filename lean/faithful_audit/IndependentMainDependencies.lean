import Karlin.FaithfulMain
import Lean.Util.CollectAxioms

namespace Karlin.IndependentMainAudit
open Filter Topology

/-- Independent restatement of the unconditional standard-gap conclusion.
No Clock, induction callback, trajectory or gap premise is supplied. -/
theorem unconditional_all_orders (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
      (a : ℕ → Fin (m+1)) (c : ℝ),
      m+1 = (k+1)^2-5 ∧ IsSkewSymmetric M ∧ a 0 = 0 ∧
      (∀ i, FaithfulMain.counts a 0 i = 0) ∧
      IsStrictTwoPlayerFPTrajectory M a a ∧
      (∀ row col, IsWeakTwoPlayerFPTrajectory M row col → row 0 = 0 → col 0 = 0 →
        ∀ t, row t = a t ∧ col t = a t) ∧
      0 < c ∧
      Tendsto (fun t : ℕ => (standardDualityGap M a a t : ℝ) *
        (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 c) ∧
      ((fun t : ℕ => (standardDualityGap M a a t : ℝ) /
        (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
        =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ))))) ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
        (c/2) * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤ (standardDualityGap M a a t : ℝ) ∧
        (standardDualityGap M a a t : ℝ) ≤ (2*c) * (t : ℝ) ^ (-(1 / (k : ℝ))) :=
  FaithfulMain.main_theorem k hk

end Karlin.IndependentMainAudit

open Lean in
run_cmd do
  let env ← getEnv
  let directRoots := #[`Karlin.FaithfulMain.main_theorem,
    `Karlin.FaithfulMain.admissible, `Karlin.FaithfulLift.nextAdmissible,
    `Karlin.FaithfulLift.principal_parent,
    `Karlin.IndependentMainAudit.unconditional_all_orders]
  for root in directRoots do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError m!"DISALLOWED AXIOM {root}: {ax}"
    for dep in state.visited do
      let s := dep.toString
      if s.startsWith "Karlin.grounded" || s.startsWith "Karlin.unconditional" ||
          s.startsWith "Karlin.all_orders_unconditional" || s.startsWith "Karlin.paper_thm_1_1_main" then
        throwError m!"FORBIDDEN DEPENDENCY {root}: {dep}"
    for dep in state.visited do
      let s := dep.toString
      for forbidden in #["groundedBundleTower", "GroundedClockBundle", "unconditionalRealizedClock",
          "all_orders_unconditional_karlin_theorem", "unconditional_karlin_theorem",
          "paper_thm_1_1_main"] do
        if (s.splitOn forbidden).length > 1 then
          throwError m!"FORBIDDEN SUBSTRING DEPENDENCY {root}: {dep}"
    logInfo m!"ENTRY_POINT {root}: axioms={state.axioms.toList}; no_grounded_or_old_main=true; broad_substrings_checked=true"
    if root == `Karlin.FaithfulMain.main_theorem then
      for required in #[`Karlin.FaithfulSeedAdmissible.rpsAdmissible,
          `Karlin.FaithfulLift.nextAdmissible,
          `Karlin.FaithfulNextClockAssembly.nextRaw,
          `Karlin.FaithfulController.secondScale,
          `Karlin.FaithfulNextTables.prescribedT2,
          `Karlin.FaithfulRealization.exact_gap_limit,
          `Karlin.FaithfulRateError.standard_gap_from_phase_tables_relative_error] do
        unless state.visited.contains required do
          throwError m!"MISSING ACTUAL CONSTRUCTION DEPENDENCY {required}"
        logInfo m!"ACTUAL_CONSTRUCTION_DEPENDENCY {required}: present"
  let namespaces := #[`Karlin.FaithfulMain, `Karlin.FaithfulLift,
    `Karlin.FaithfulNextAdmissible, `Karlin.FaithfulFamily,
    `Karlin.FaithfulGameReindex, `Karlin.IndependentMainAudit]
  let mut total := 0
  let mut state : Lean.CollectAxioms.State := {}
  for root in namespaces do
    let mut count := 0
    for (name, _) in env.constants.toList do
      if root.isPrefixOf name then
        count := count + 1
        let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
        state := next
    total := total + count
    logInfo m!"NAMESPACE {root}: declarations={count}"
  for ax in state.axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError m!"DISALLOWED AXIOM {ax}"
  for dep in state.visited do
    let s := dep.toString
    if s.startsWith "Karlin.grounded" || s.startsWith "Karlin.unconditional" ||
        s.startsWith "Karlin.all_orders_unconditional" || s.startsWith "Karlin.paper_thm_1_1_main" then
      throwError m!"FORBIDDEN DEPENDENCY {dep}"
  for dep in state.visited do
    let s := dep.toString
    for forbidden in #["groundedBundleTower", "GroundedClockBundle", "unconditionalRealizedClock",
        "all_orders_unconditional_karlin_theorem", "unconditional_karlin_theorem",
        "paper_thm_1_1_main"] do
      if (s.splitOn forbidden).length > 1 then
        throwError m!"FORBIDDEN SUBSTRING DEPENDENCY {dep}"
  logInfo m!"MAIN_AUDIT declarations={total}; axioms={state.axioms.toList}; no_grounded_or_old_main=true; broad_substrings_checked=true"

#check @Karlin.FaithfulMain.main_theorem
