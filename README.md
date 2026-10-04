# Alpha experiments

Exact, reproducible computations for the RPS-based simultaneous fictitious-play construction of orders 2–6. The installed games have 4, 11, 20, 31, and 44 actions, respectively.

All action choices, score updates, run boundaries, and sign certificates use integers or exact rational numbers. Floating-point values are used for descriptive logarithms, plotting, elapsed-time budgets, and optional log-time stopping, never to select an action or certify a sign. Higher-order logarithms and ratios use Decimal arithmetic.

## Quick start

Use Python 3.11 or newer. The release was tested with Python 3.12.14 on Linux. Run these commands from the repository root:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-lock.txt
python reproduce.py smoke --output-dir outputs/smoke
python reproduce.py figures --output-dir outputs/figures
```

On Windows, activate with `.venv\Scripts\activate`.

The standard-library exact replay and certificate checks do not need third-party packages. SymPy is required to reconstruct the games; NumPy and Matplotlib are required for figures. `requirements.txt` pins the three direct dependencies; `requirements-lock.txt` also pins their transitive dependencies for the tested environment.

Each reproduction command requires a **new output directory**. It copies the computational inputs there, writes separate logs, and produces `run_report.json`. Bundled reference evidence is never overwritten by this entry point. Run without `-O` or `-OO`: verification modules reject optimized Python because it disables assertions.

## Reproduction levels

```sh
# Tests, exact matrix/count/score/gap checks, and leading constants
python reproduce.py smoke --output-dir outputs/smoke-2

# Rebuild the matrices and compare every construction field except runtime
python reproduce.py construct --output-dir outputs/construction

# Fresh low-order runs and complete finite higher-order certificates
python reproduce.py replay --output-dir outputs/replay

# Independent arithmetic and full-horizon sign checks on the supplied evidence
python reproduce.py audit --output-dir outputs/audit

# Redraw the two figures from supplied evidence; no simulation is run
python reproduce.py figures --output-dir outputs/figures-2

# Rebuild, replay, independently audit the fresh outputs, and plot them
python reproduce.py all --output-dir outputs/full
```

Short checks take seconds. Complete replay/audit runs take minutes and may take longer on other machines; order 6 uses very large exact integers. See [AUDIT.md](AUDIT.md) for measured timings and the precise tests actually run. Logs are retained if a stage fails. Reusing an existing output directory is deliberately refused.

The full pipeline compares freshly generated construction data and final states with the supplied reference data. For orders 2–3 it compares the entire result, including every sampled value, excluding elapsed time. For orders 4–6 it compares all final exact counts, scores, times, normalization data, and sampled values; certificate implementation hashes and runtimes are allowed to change.

## Experiment conventions

- The game matrix is skew-symmetric. Both players start with one prescribed common setup action at completed time `t = 1`
- Subsequent choices are simultaneous and uniquely optimal. The implementation rejects a tie; it does not silently invent a tie-breaking rule
- Both players have identical empirical count vectors. If `B = D A` is the integer-scaled matrix and `s = B counts`, the unnormalized gap is `2 max(s) / (D t)`
- Dividing the game by its maximum absolute matrix entry does not change action choices. The normalized gap is `2 max(s) / (max(abs(B)) t)`
- Order 2 uses exactly 100,000 certified events, the archived `2**40` cycle cap, and the archived stride-10 sampling. Order 3 uses exactly 1,000,000 events and stride-100 sampling. The first 128 events and final state are also sampled. These are the publication-v5 settings
- Orders 4–6 certify the entire finite word from phase `Q` through phase `4096 Q`, for `4095 Q` completed outer phases

An event can represent a maximal constant-action run or a certified batch of RPS cycles. An event count is not a count of rounds. The first setup action is included in all reported times.

## What the figures establish

The order-2/3 plots show selected event-endpoint observations from exact replay. The order-4/5/6 plots show **outer-phase boundary samples** extracted from a certified finite word. The certificate covers every skipped decision within its finite horizon, but the plotted samples do not show every round or the within-phase shape. Connecting segments are visual guides.

The dashed laws use constants computed from exact leading coefficients, rather than fitted slopes. A finite run or certificate is not an infinite-time proof. A Bernstein result of `NOT_CERTIFIED` means this sufficient certificate failed; it is not by itself a counterexample. No setup-free cubic asymptotic rate is claimed here.

The reproduced PDFs and PNG previews are included in [figures/](figures/README.md).

Figure generation verifies SHA-256 fingerprints of all 17 plotted numeric line arrays against the bundled publication arrays. It writes PDFs, PNG previews, and `plot_data_verification.json`. Numeric arrays are the reproducibility target; PDF bytes may depend on fonts and plotting-library versions.

## Layout

- `computations/construction.py`: exact symbolic construction and algebraic checks
- `computations/exact_events.py`: exact event replay and finite quadratic cycle certificates
- `computations/hierarchical/`: finite-word polynomial certificates and replay
- `computations/audit/` and `computations/hierarchical/audit/`: independent arithmetic and monomial/Faulhaber implementations
- `computations/order*_construction.json`: exact matrices, coefficient tables, parameters, and rate constants
- `computations/*result.json` and `computations/hierarchical/*.json`: supplied numerical reference evidence
- `computations/plots/`: deterministic numeric-array verification and plotting
- `tests/`: helper, oracle, certificate, invalid-input, and optimized-Python regressions
- `examples/exact_prefix.py`: a 1,000-round direct-versus-event comparison
- `provenance/source_files.json`: input-file hashes and source-to-release mapping

The `computations` scripts write beside themselves and are implementation entry points; use `reproduce.py` for isolated runs. For a direct short example:

```sh
python examples/exact_prefix.py
python -m unittest discover -s tests -v
```

This repository contains code and numerical evidence only. No manuscript, correspondence, or publication destination is required to run it. No license has been selected for this release.

## Extended cubic run (v10)

The original audited baseline above remains unchanged. [extensions/cubic-v10](extensions/cubic-v10/README.md) contains the extended 2,000,000-event cubic run, its complete compressed transcript, independent full decision audit, and revised figures. It reaches t = 16,727,255,004,807,900,625,001 with a relative deviation from the leading cubic law of about 0.00005163846. This is a finite computation, not an infinite-time convergence proof.

```sh
python extensions/cubic-v10/assemble_transcript.py
python extensions/cubic-v10/verify_extension.py
python extensions/cubic-v10/verify_full_cubic.py
python extensions/cubic-v10/replot_v10.py --data-root extensions/cubic-v10 --output-dir outputs/figures-v10
```

The compressed cubic transcript is stored as five byte-exact parts for reliable transfer. Before transcript verification, reconstruct it once:

```sh
python extensions/cubic-v10/assemble_transcript.py
```

This checks every part and the complete original SHA-256. The joined file is generated locally and ignored by Git.
