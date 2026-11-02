import Karlin.FaithfulV15
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean in
run_cmd do
  let env ← getEnv
  let old := #[`Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan,
    `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests,
    `Karlin.FaithfulCokernel.binomialKernelBasis,
    `Karlin.FaithfulCokernel.dividedPowerKernelBasis,
    `Karlin.FaithfulGrowthRecurrences.bundle_sum_expansion,
    `Karlin.FaithfulGrowthRecurrences.polynomial_height_expansion,
    `Karlin.FaithfulScale.binomial_row_integral_of_values]
  let roots := #[`Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff,
    `Karlin.FaithfulPaperAlgebra.clock_bundle_expansion_by_ordinary_powers,
    `Karlin.FaithfulPaperAlgebra.height_expansion_by_degree_drop,
    `Karlin.FaithfulPaperAlgebra.chosenCorrection_forward_difference_formula]
  let reqs := #[
    #[`Karlin.FaithfulPaperCokernel.D_pow_zero,
      `Karlin.FaithfulPaperCokernel.exp_D_apply,
      `Karlin.FaithfulPaperCokernel.one_sub_exp_neg,
      `Karlin.FaithfulPaperCokernel.expFactor_geometric_inverse,
      `Karlin.FaithfulPaperCokernel.conjugate_adjoint,
      `Karlin.FaithfulPaperCokernel.symmetric_derivation_expansion,
      `Karlin.FaithfulPaperCokernel.paper_binomial_kernel_mem_span],
    #[`Karlin.FaithfulPaperAlgebra.ordinary_power_bundle_expansion,
      `Karlin.FaithfulPaperAlgebra.polynomial_bundle_remainder],
    #[`Karlin.FaithfulPaperAlgebra.backwardDifference_degree_and_leading,
      `Karlin.FaithfulPaperAlgebra.height_polynomial_degree_by_backward_difference],
    #[`Karlin.FaithfulPaperAlgebra.binomial_row_integral_by_differences,
      `Karlin.FaithfulPaperAlgebra.forward_difference_formula,
      `Karlin.FaithfulPaperAlgebra.chosenCorrection_cast_by_differences]]
  for i in [:roots.size] do
    let root := roots[i]!
    let (_, st) := ((Lean.CollectAxioms.collect root).run env).run {}
    for n in old do
      if st.visited.contains n then throwError m!"OLD_ROUTE {root} {n}"
    for n in reqs[i]! do
      unless st.visited.contains n do throwError m!"MISSING_STEP {root} {n}"
    logInfo m!"ROUTE_PASS {root}: closure={st.visited.size}, axioms={st.axioms.toList}, required={reqs[i]!}"
  let effective := #[`Karlin.FaithfulEffectiveContract.lift_every_partrec_parent_program,
      `Karlin.FaithfulEffectiveContract.universal_clock_program]
  for root in effective do
    let (_, st) := ((Lean.CollectAxioms.collect root).run env).run {}
    for n in #[`Karlin.FaithfulEffectiveContract.UniversalProgram.evaln_complete,
      `Karlin.FaithfulEffectiveContract.UniversalProgram.evaln_sound,
      `Karlin.FaithfulEffectiveContract.UniversalThresholdRealizer.runCode_correct] do
      unless st.visited.contains n do throwError m!"MISSING_INTERPRETER_PROOF {root} {n}"
    logInfo m!"EFFECTIVE_PASS {root}: closure={st.visited.size}; axioms={st.axioms.toList}"
  for root in #[`Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem] do
    let (_, st) := ((Lean.CollectAxioms.collect root).run env).run {}
    logInfo m!"MAIN_ROUTE {root}: oldCokernel={st.visited.contains `Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests}, newCokernel={st.visited.contains `Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff}"
