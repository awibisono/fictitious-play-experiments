# Main technical statement and proof-route crosswalk

Upstream source revision: `23f53ae238d01b1be52c981434c6abaef5cd49c9`.
Historical manuscript reference:
[arXiv:2610.08768v1](https://arxiv.org/abs/2610.08768v1).
This is a public summary of the audited baseline, **not a newly checked v19
crosswalk**. Inline references to v12, v15, page numbers, section numbers, and
`master_v15` in the preserved source identify historical mathematical locators;
they are not assertions about the pagination or wording of the latest manuscript.

The source files below are in `Karlin/`. Verification probes are in
`verification/probes/`; their current execution status is separate from their
presence in the package.

| Claim or route | Source and actual consumer | Independent check |
| --- | --- | --- |
| Main and smaller families; strict simultaneous play; setup-inclusive gap; exact constant and all-integer relative error | [`FaithfulMain.main_theorem`](Karlin/FaithfulMain.lean), [`FaithfulSevenFamily.main_theorem`](Karlin/FaithfulSevenFamily.lean), [`FaithfulRealization.exact_gap_limit` and `relative_gap_error`](Karlin/FaithfulRealization.lean) | `IndependentWholeGate.lean` restates raw cumulative counts, score inequalities and max-minus-min gap; checks trust closure. |
| One finite program before all positive rational inputs, with the same threshold and suffix guarantee | [`FaithfulEffectiveContract`](Karlin/FaithfulEffectiveContract.lean): `UniversalThresholdRealizer`, `lift_every_partrec_parent_contract`, `lift_every_partrec_parent_program`, `universal_clock_contract`, `universalRpsFamily`, `universalSevenFamily` | `IndependentContracts.lean`; the realizer is additional data beyond raw `Clock`. |
| Fixed scales before phases/prefixes; strictness and reset endpoints | [`FaithfulPaperCoverage.chosen_strictness` and `selected_chronology`](Karlin/FaithfulPaperCoverage.lean), [`FaithfulPaperChronology`](Karlin/FaithfulPaperChronology.lean), actual reset/clock assembly | Main statement and route gates; reset-start ties are distinguished from strict play after the first parent action. |
| Finite-difference integrality | [`FaithfulFiniteDifference.forward_difference_formula` and `binomial_row_eq_forward_difference`](Karlin/FaithfulFiniteDifference.lean) feed [`FaithfulScale.binomial_row_integral_of_values`](Karlin/FaithfulScale.lean) | Remaining gate checks actual consumers and direct proof edges. |
| Ordinary-power bundle growth and backward degree drop | [`FaithfulPolynomialRoutes.bundle_row_top_coefficient` and `backwardDifference_top_coefficient`](Karlin/FaithfulPolynomialRoutes.lean) feed `FaithfulInheritance.oldLengthRow_last_pos` and `FaithfulTables.zeta_leading` | Remaining gate checks the specified polynomial route and excludes alternative dependencies. |
| Neighboring-phase ratios and uniform all-integer interpolation | [`FaithfulRateError.polynomial_successor_ratio_error` → `within_phase_ratio_error` → `interpolated_polynomial_error`](Karlin/FaithfulRateError.lean) → both final realization limits/errors | Remaining gate and final-family closures; leading positivity is derived from the existing premises. |
| Literal coefficient norm, internal sums, and downstream signs | [`FaithfulNormStar.internal_norm_sum_bound`](Karlin/FaithfulNormStar.lean) → [`FaithfulBounds`](Karlin/FaithfulBounds.lean) → [`FaithfulEffectiveParameters`](Karlin/FaithfulEffectiveParameters.lean) | Remaining gate checks the stated norm route and its use in parameter certificates. |
| Pre-gateway suffix with exact `c-delta` | [`FaithfulGatewaySuffix.actual_pre_gateway_gain` and `terminal_prefix_gain`](Karlin/FaithfulGatewaySuffix.lean) → [`FaithfulActualSuffix.actual_suffix`](Karlin/FaithfulActualSuffix.lean) | Remaining gate checks the proper-prefix case without assuming completed child-clock validity. |
| Nilpotent/exponential cokernel argument and lift assembly | [`FaithfulPaperCokernel.paper_momentSection_solves`](Karlin/FaithfulPaperCokernel.lean) → compatibility/moment tables → successor clock/admissibility → both families | `IndependentAssemblyGate.lean`: assembly stages, direct proof edges, required route nodes and excluded alternatives. |
| Essential seeds, induction, general Appendix A bounds | Faithful RPS/seven seed and admissibility modules; [`FaithfulFamily`](Karlin/FaithfulFamily.lean), [`FaithfulLift`](Karlin/FaithfulLift.lean), [`FaithfulAppendixBounds`](Karlin/FaithfulAppendixBounds.lean), [`FaithfulAppendixActual`](Karlin/FaithfulAppendixActual.lean), [`FaithfulAppendixSearch`](Karlin/FaithfulAppendixSearch.lean) | Statement/contract probes, route checks, and whole trust scan. |
| Seven-action cubic base and smaller-family dimension | [`FaithfulSevenSeed.sevenClock`](Karlin/FaithfulSevenSeed.lean) has six recurrent actions; [`FaithfulSevenFamily`](Karlin/FaithfulSevenFamily.lean) adds the setup action and proves `(k+1)^2 - 9` total actions | Smaller-family statement and dependency checks. |
| Full-matrix payoff normalization | [`FaithfulConsequences`](Karlin/FaithfulConsequences.lean): `maxEntry`, `normalizedMatrix`, normalized constant, exact gap, relative error and rational power formula | Normalization uses the full setup-inclusive matrix, not only the recurrent block. |

The scope excludes illustrative numerical instances, simulations, practical
extraction complexity, blanket literature correctness, and a separate
universal-machine representation theorem for the host order-to-code compiler.
See [README.md](README.md) for computational quantifiers and reproduction limits.
