# Two superseded historical dependency checks

The public export omits exactly these two historical audit harnesses:

- `faithful_audit/revised/RevisedGateAudit.lean`
- `faithful_audit/revised/RevisedSevenGateAudit.lean`

Their original hashes and the omission rationale are recorded in
[`../provenance/SOURCE_MAP.json`](../provenance/SOURCE_MAP.json). The original
archive and the failed diagnostic logs remain preserved in the private review
record. All 95 mathematical library source files remain in this export.

## Why the dependency assertion is stale

Both harnesses require the final-family proof closure to contain
`Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests`. The current audited
proof route instead uses
`Karlin.FaithfulPaperCokernel.paper_moment_solvable_iff`, through the
nilpotent/exponential completeness argument.

The included `IndependentAssemblyGate.lean` requires that current route and
explicitly excludes the older alternative from the final construction.
`IndependentRouteGate.lean` checks the corresponding route distinction. The
preserved original audit already recorded `oldCokernel=false` and
`newCokernel=true` for both families; this distinction was not caused by public
documentation cleanup. The two historical harnesses therefore fail an obsolete
**required-dependency assertion**, not a mathematical theorem.

The older theorem is not declared false or invalid. The stale assertion is that
the final proof must depend on it. No mathematical proof was changed to satisfy
or bypass these checks.

## Current coverage

`IndependentWholeGate.lean` independently restates both historical raw main
statements: cumulative counts, the empirical max-minus-min gap, and strict
row/column best-response inequalities. It also checks the seeds, lift,
chronology, moment-section use, suffix guarantee, exact/all-time error, and
logical trust closure. `IndependentAssemblyGate.lean` checks the current section
solution's exact unrestricted proposition; the construction retains its `k=0`
case. Thus the semantic checks are not discarded merely to remove a failing
historical dependency expectation.

The preliminary expanded reproduction passed the project build and all six
current independent probes, then failed in a superseded harness. That run is
not relabeled as an aggregate success. A complete clean reproduction of the
final exported source set and its eight retained companions is required and is
reported separately in `STATUS.json`.
