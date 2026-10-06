# Audit and verification

Audit date: 3 October 2026. This release was prepared separately from its input archive. Input matrices and saved numerical evidence were preserved. No numerical discrepancy was found in the finite scopes below. Defensive and reproducibility defects were found and corrected; see [CHANGES.md](CHANGES.md).

## Mathematical checks

### Exact event replay

For a strict leader `a` with zero diagonal, each rival's score difference is affine during an `a` run. The run length is the minimum positive integer at which a rising rival catches the leader. Checking the first and last included decisions therefore covers every intermediate decision.

The RPS batch proposes lengths `ell_a + 3r`. Its doubled cycle-start score is `2s + (2d0-d1)r + d1 r²`. The implementation certifies all first/last run margins against every action, including setup, over the complete finite integer cycle-index interval. Independent tests use direct integer scans and discrete convexity/binary search rather than the production square-root or run-length formulas.

The low-order tests include:

- 55,080 exhaustive small-coefficient first-nonpositive cases
- 532 additional large-integer cases, including 1,000-digit roots, double roots, and convex intervals containing no nonpositive integer
- 12,000 brute-force quadratic-minimum cases and six large-vertex cases
- More than 3,000 random strict constant-action runs and 10,000 direct simultaneous rounds
- 1,200 installed candidate events, independently replaying 39,357 constituent runs and visiting every active action in both games
- Publication-cap activation, JSON/transcript round trips, exact matrix/count/score/time/gap identities, invalid-input rejection, and refusal of optimized Python

Fresh full publication-mode runs reproduce all 10,117 order-two and 10,128 cubic samples, together with every other archived non-timing field. Their final completed times are respectively `53022640904073249730911428245962751` and `2134395777450825312501`.

### Hierarchical finite-word certificates

The count tables are derived by summing the proposed nested word. The reset-length and stride tables propose that word; they do not authorize a best response. Every proposed run contributes exact first/last margins against every installed rival and a nonnegative length-minus-one constraint. Ancestor-dependent finite index ranges are mapped into a unit cube. Exact nonnegative tensor Bernstein coefficients are a sufficient certificate there; strict margins require strictly positive coefficients.

The independent implementation uses its own monomial/Faulhaber sums and a different coefficient-conversion algorithm. It does not read the supplied `C` or `R` tables to establish the signs. Additional tests compare every count/margin/domain polynomial for orders 2–4, test Faulhaber sums against direct integer sums, compare random rational tensor conversions against the direct basis formula, and exercise strict-zero and positive-but-not-Bernstein-certified cases.

Complete independent sign recomputation covers `Q <= q < 4096 Q`:

| Order | Installed actions | Inequalities | Exact Bernstein coefficients |
|---|---:|---:|---:|
| 4 | 20 | 743 | 8,389 |
| 5 | 31 | 1,833 | 74,137 |
| 6 | 44 | 3,745 | 691,406 |

Saved higher-order samples, counts, scores, gaps, normalization, rate constants, ratios, and secants are also reconstructed independently from word sums. The sextic dense-sample check verifies its source-horizon linkage. Archived sextic prefix certificates overlap; interval-union validation is used rather than adding their lengths. The new sextic runner recomputes one certificate for the entire horizon and does not trust a cached `PASS`.

### Construction and figures

Every construction for orders 2–6 is rebuilt from the symbolic implementation and compared field by field with the supplied data, excluding runtime. Separate constructor regressions verify the implemented algebra, finite-degree polynomial identities, selected exact radius identities, and 64 actual post-setup decisions per order. These finite checks are not an all-order theorem proof.

The two figure layouts reproduce all 17 numerical line-array fingerprints. PNGs were visually inspected for labels, clipping, and legend placement. The higher-order figure is explicitly labeled as boundary observations; connecting lines are not additional certified observations.

## Fresh environment and recorded runs

The tests use a newly created virtual environment without inherited system packages, on Linux with Python 3.12.14. Exact direct dependencies are SymPy 1.14.0, NumPy 2.3.5, and Matplotlib 3.10.8. All runtime transitive versions are pinned in `requirements-lock.txt`.

The final full run passed in **1,040.2 seconds (17 minutes 20 seconds)**. The final smoke run, including all **33 tests**, passed in 7.2 seconds. The unit suite also passed on Python 3.13.5. Representative stage times were:

| Stage | Seconds |
|---|---:|
| Symbolic constructor regression through order 6 | 281.7 |
| Fresh matrix reconstruction through order 6 | 147.2 |
| Full order-two replay | 9.8 |
| Full cubic replay | 83.4 |
| Orders 4–5 finite certificates | 56.8 |
| Fresh full-horizon sextic certificate | 175.2 |
| Independent full-horizon sextic sign pass | 164.2 |
| Figure generation and all-array verification | 9.5 |

The machine-readable verification record and complete stage logs are in `verification/`. Wall times are machine-specific. The repository's `all` stage reconstructs games, runs finite replays, audits the fresh outputs independently, and regenerates the figures in an isolated directory.

## Corrected defects

1. The original reproduction instructions used the generic order-two engine, which lacks the archived cap and sampling cadence. The first independently observed saved-sample divergence occurs at event 1331. The release entry point explicitly selects publication-v5 settings
2. Negative cycle caps or round counts could produce backward updates; they are now rejected before state mutation
3. Matrix SHA-256 values were copied without validation; the loader now verifies the digest, exact representation, dimensions, order, and skew symmetry
4. Zero event budgets and malformed domains produced unrelated exceptions or invalid behavior; explicit domain checks now fail early
5. Assertion-based certificates could be run with Python optimization; all verification modules now refuse that mode
6. Standalone certificate commands could report `NOT_CERTIFIED` in JSON but exit successfully, creating a false-success risk in shell pipelines. They now preserve diagnostics and fail explicitly; injected-failure tests cover all three CLI paths
7. Integrity checks now bind the result phase origin to the construction and reject empty or gapped certificate intervals, with regression tests
8. The supplied sextic continuation depended on a historical engine hash and cached prefix `PASS`; the release recomputes the complete interval instead

Valid publication data and exact construction formulas were unchanged by these corrections. Formatting and descriptive naming do not alter arithmetic.

## Limits

- This is a finite computational audit, not a formal proof assistant verification or a proof of the infinite all-order theorem
- Direct round-by-round replay is feasible only for short prefixes. Large finite horizons are covered by exact polynomial certificates
- The independent high-order verifier shares the installed matrix, reset-length tables, and stride parameters, while independently deriving counts and decision inequalities
- A failed sufficient Bernstein certificate is inconclusive about the underlying trajectory inequality
- Plotted low-order event samples and high-order phase boundaries do not resolve every round or establish within-phase asymptotic shape
- No setup-free cubic rate is established
- Matrix digests detect accidental mismatch; they are not signatures or an independent proof of construction
- The complete scientific workflow was exercised on Python 3.12.14 on Linux; the standard-library unit suite was also exercised on Python 3.13.5. The supplied Python 3.11/3.12 CI workflows were prepared, not executed on a hosted service as part of this local audit
- PDF byte identity is not promised across font/rendering environments; all 17 numerical arrays are fingerprint-checked

## Publication-readiness recheck — 6 October 2026

A fresh isolated checkout was exercised on macOS with Python 3.14.7 and the pinned runtime dependencies from `requirements-lock.txt`. The 36-test suite, direct 1,000-round example, symbolic reconstruction through order 6, complete baseline replay for orders 2–6, independent finite-horizon audits, and both figure-generation pipelines passed. Baseline replay compared all exact reference states and samples; construction took 409.9 seconds, full replay took 320.6 seconds, and the independent audit took 250.0 seconds on this machine. The extended cubic transcript was independently verified through all 2,000,000 events and 95,051,875,000 represented runs; its reported endpoint and relative deviation were reproduced. These are finite-scope checks, with the limitations above unchanged.

The recheck found a portability defect in strict comparisons of descriptive floating-point logarithms: platform math-library rounding differed by at most `1.1e-14` in the fresh runs. Comparisons now allow an absolute `1e-12` difference only for `log10_t`, `log10_gap`, and `log10_normalized_gap`. Every other replay field remains exact. Regression tests reject changed counts, rational gaps, types, structure, nonfinite values, and materially changed logs. For the combined pipeline, a separate plotting copy uses the archived logarithms after that comparison, preserving all 17 numeric-array fingerprints without changing raw replay results.

Five supplemental scripts were formatted for readability with identical Python syntax trees before and after formatting. A machine-specific interpreter path in the archived resource report was replaced by the portable label `python`; measured resource values were preserved. Scientific explanations, numerical evidence, original provenance, and the exact simulation engines were retained. The README now distinguishes the original baseline from the extended-run figures near the top.

Both reachable commits and all 99 unique historical file blobs were inspected with credential/private-link patterns and manual review of text, numerical schemas, transcript contents, and figure metadata. No secrets or private correspondence were found. This is a bounded review rather than a guarantee that arbitrary sensitive information can never escape detection. No history was rewritten, and no software license was selected.

The stages were run separately; the single `all` command was not rerun end to end during this recheck. Its fresh-replay plotting preparation was exercised on the completed replay outputs and in a raw-output-preservation regression. The extended two-million-event simulation and Linux-only bounded-resource wrapper were not rerun; the complete saved extension transcript was independently checked instead. Original measured timings remain historical evidence, not performance guarantees for other machines.
