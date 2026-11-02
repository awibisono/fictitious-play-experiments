# Lean formalization of On Karlin's Conjecture for Fictitious Play

This directory contains the Lean 4 formalization and independent verification
probes for the main technical constructions in the paper. It is independent of
the Python experiments elsewhere in the repository.

**Verified release artifact:** the final clean reproduction passed on
2 November 2026: a 3,205-job project build, nine pinned dependency checks, six
independent probes, and eight companion checks. There were 18 non-proof-hole
linter warnings and no errors. See the [fresh verification report](verification/FRESH_VERIFICATION.md)
and [`verification/STATUS.json`](verification/STATUS.json) for exact scope,
identities, and logs. No software license has been specified.

## Scope

The principal statements are
[`Karlin.FaithfulMain.main_theorem`](Karlin/FaithfulMain.lean) and
[`Karlin.FaithfulSevenFamily.main_theorem`](Karlin/FaithfulSevenFamily.lean).
They establish two families of rational skew-symmetric games with respectively
`(k + 1)^2 - 5` actions for `k ≥ 2` and `(k + 1)^2 - 9` actions for `k ≥ 3`.
The conclusions concern zero initial counts, one prescribed common setup action,
strict simultaneous fictitious play thereafter, the setup-inclusive empirical
gap, an exact positive leading constant, and relative `O(t^(-1/k))` error at all
integer times. Strictness is not asserted at the unavoidable initial tie.

The reviewed scope includes the essential seeds, inductive construction,
every-prefix chronology, fixed-parameter quantifier order, and general
Appendix A bounds. See the [statement and proof-route crosswalk](CROSSWALK.md).
Illustrative Appendix B numerical instances, Appendix C simulations, and blanket
correctness of the literature discussion are outside this certificate. The Lean
proofs do not certify the separate Python implementations or their plotted data.

### Computational contract

The computational results require a `UniversalThresholdRealizer` in addition to
the mathematical `Clock` interface. For an admissible parent with such a
realizer, one finite `UniversalProgram` code is selected **before all positive
rational inputs**. It computes the same threshold and preserves the suffix
guarantee; terminating interpreter fuel may depend on the input. `runCode`
performs automatic fuel search. Both concrete families supply verified
realizers and constructors uniform in `k`.

This is not a claim about practical extraction speed, bit complexity, or
large-order runtime. A separate `Nat.Partrec` representation theorem for the
host order-to-code compiler is not included.

## Reference version and provenance

The original audited source revision is
`23f53ae238d01b1be52c981434c6abaef5cd49c9`. Its historical manuscript reference is
the source of [arXiv:2610.08768v1](https://arxiv.org/abs/2610.08768v1), reconciled
with the audit on 11 October 2026. Page numbers in the crosswalk refer to that
version, not to a later manuscript rendering.

**Current v19 correspondence:** the central mathematical statements and
computational qualifications were checked against source-bound extracts of
current v19, with no discrepancy found in that scope. This includes both family
statements, simultaneous-play and empirical-gap definitions, the setup action,
the exact leading constant and all-integer-time error, and the realizer and
program-quantifier qualifications. See the [current correspondence review](verification/V19_CENTRAL_CORRESPONDENCE.md)
for the exact source revision and checked clauses. This is not a renewed
whole-manuscript proof audit or a refreshed complete statement-by-statement
crosswalk. The historical audit remains summarized in
[the audit record](verification/HISTORICAL_AUDIT.md).

[`provenance/SOURCE_MAP.json`](provenance/SOURCE_MAP.json) records each included
upstream source path, original hash, public path, and public hash.
[`provenance/EXPORT_CHANGES.json`](provenance/EXPORT_CHANGES.json) distinguishes
documentation cleanup from any source-comment changes. Original mathematical
declarations and proofs are not intentionally changed by the public export.
The upstream revision is provenance, **not** the eventual hosting-repository
commit. A public citation must use the actual publication commit when one exists.

## Reproduce

Requirements: Python 3, Git, Bash, and
[elan](https://github.com/leanprover/elan). Network access and sufficient disk
space are needed for the pinned Lean toolchain and mathlib dependencies.

From this directory:

```sh
python3 VERIFY_PACKAGE.py
elan toolchain install leanprover/lean4:v4.27.0
bash REPRODUCE.sh
```

The script verifies the release manifest, checks the toolchain, cleans the local
project build, builds with the preserved lockfile, verifies dependency revisions
and tracked source cleanliness, runs the six independent probes, and typechecks
the three root route-verification files and five retained `faithful_audit/`
companion files. These eight companion files are not assumed to be covered by
the default Lake target. It records command logs and a machine-readable result in a new `reproduction-output/`
directory. Existing output directories are refused; choose a new directory for
another run, for example `bash REPRODUCE.sh /tmp/karlin-check-2`.

Do not run `lake update`: this release targets Lean 4.27.0 and the exact revisions
in `lake-manifest.json`, including mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Dependency caches may accelerate a build
but must match those revisions. Compiler warnings are recorded, not silently
discarded; the historical audit did not imply a zero-warning build.

`VERIFY_PACKAGE.py` checks file identity and exported-source provenance, not
mathematical correctness. `lake build` alone is also not the whole verification
procedure: the independent gates inspect statements and transitive dependency
closures. Their allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

The historical cross-revision preservation comparison additionally required an
older source checkout and audit workspace. Those are not distributed here, and
this script does not claim to rerun that comparison.

Two historical audit harnesses required a dependency route that the current
audited construction deliberately replaced. They are not included as current
checks; their semantic and trust checks are covered by the included independent
gates. The old theorem itself is not invalidated. See the explicit
[superseded-check record](verification/SUPERSEDED_CHECKS.md).

## Layout and publication policy

- `Karlin/`, `Karlin.lean`: mathematical project sources.
- Root and `faithful_audit/` Lean files: retained verification sources.
- `verification/probes/`: six independent gate and inventory sources.
- `verification/`: clearly separated historical and fresh verification status.
- `provenance/`: source mapping and export-change accounting.
- `PUBLICATION_MANIFEST.json`: hashes for this public layout.

Build products, toolchains, vendored dependencies, manuscript dumps, private
project links, correspondence, and internal progress reports are not part of
this source release. No license is inferred from the dependency licenses;
the authors must select the licensing terms before describing this as an
open-source release. See [LICENSE_STATUS.md](LICENSE_STATUS.md).
