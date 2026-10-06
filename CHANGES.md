# Release changes

## Reproducibility and layout

- Selected the publication-compatible event implementation as the single canonical event engine
- Renamed the symbolic constructor and construction driver to descriptive, version-independent names
- Added isolated, logged reproduction stages, exact reference comparisons, pinned dependencies, tests, and a small example
- Removed manuscript-dependent checks, editorial artifacts, and setup-free exploratory material from the package
- Replaced cached sextic continuation with a fresh certificate for the complete finite horizon before extracting observations
- Labeled the higher-order plotted observations as boundary samples
- Reformatted source without changing the construction formulas or publication cap/stride settings

## Verified defensive fixes

- Exact modules reject optimized Python so assertions cannot be silently disabled
- The event loader validates matrix shape, skew symmetry, and its recorded SHA-256 before execution
- Negative batch caps and horizons, zero event budgets, and other unsupported inputs fail with clear errors instead of producing backward counts or unrelated exceptions
- Standalone sign-certificate commands now return nonzero on NOT_CERTIFIED while preserving diagnostic JSON and structured callable results
- Integrity checks bind reported phase origins to the construction and reject empty or gapped certificate coverage

These fixes apply to invalid inputs, provenance validation, and reproducibility safeguards. Valid-domain exact arithmetic and archived numerical output are unchanged. Tests exercise the former failures and independent direct oracles.

## Publication-readiness cleanup — 6 October 2026

- Allow platform rounding only in descriptive replay logarithms while preserving exact scientific comparisons and raw replay outputs
- Add regressions for exact mismatches, structural changes, nonfinite logs, and plot-copy isolation
- Make the extended-run figure command prominent and remove obsolete internal version wording
- Format the supplemental scripts without changing their Python syntax trees and replace the resource report's machine-specific interpreter path with `python`
- Refresh integrity manifests; retain numerical data, useful scientific comments, provenance, and the existing no-license status
