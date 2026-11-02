# Fresh verification — 2 November 2026

**PASS for the final exported source set and documented reproduction procedure.**
This is a fresh project-source build and gate run, not merely a check of archived
logs. This report records the prepublication verification run; publication status
is separate from that result.

## Executed result

The final run started at `2026-11-02T04:32:33.922999+00:00` and finished at
`2026-11-02T05:08:24.781624+00:00`, with aggregate exit code **0**. It took
2,150.858625 seconds (about 35 minutes 51 seconds) in the tested environment.
This is a measurement, not a runtime guarantee.

- Fresh project build: **3,205 jobs**, with zero project build outputs present
  beforehand. No project proof outputs were reused.
- All **nine** dependency revisions matched the unchanged lockfile; their
  tracked sources were clean.
- All **six independent probes** and **eight retained companion checks** passed.
- Package/source-map integrity checks passed before and after execution.
- **18** build linter diagnostics, no proof-hole warnings, **zero errors**, and
  no warning/error headers in the remaining probe logs. This was not a
  warning-free build.

The runtime was Lean 4.27.0, Linux x86-64, compiler commit
`db93fe1608548721853390a10cd40580fe7d22ae`. Official pinned mathlib dependency
caches were used; this was **not** a from-source rebuild of Lean and mathlib.

## Proof and trust observations

The whole Faithful gate checked 76 modules, 3,923 declarations, and 3,085
theorems. Its union dependency closure contained 40,751 declarations; the two
main-family closures contained 37,713 and 37,779. Only `propext`,
`Classical.choice`, and `Quot.sound` appeared as logical axioms in those checks.
The gate found no forbidden, unsafe, or opaque project dependencies.

The generated 9,240-record declaration inventory exactly matched both the
separately rebuilt original artifact and the preserved historical inventory,
when indexed by declaration name. These structural fingerprints corroborate
reproduction; they are not collision-free formal equivalence proofs.

## Input identity and evidence

- Upstream source revision: `23f53ae238d01b1be52c981434c6abaef5cd49c9`.
- Tested source-map SHA-256:
  `991979fe299c26bd1531a0b620900e0efe28e3d90bb7b302a6f58dd4f38a26df`.
- Tested 125-file source-export manifest SHA-256:
  `da697e74de6013e4a05ad11194d641b7b0b1ab10b788aebdac58243426453b52`.

The [machine-readable evidence summary](fresh-2026-11-02/final-evidence-summary.json)
records the exact tested verifier/reproduction-script hashes, toolchain,
dependency revisions, counts, and log hashes. The adjoining evidence directory
contains the original fresh logs and result, copied byte-for-byte after review
for private paths and commentary. No redaction was needed in these log files.

After the run, this report, final status/readme text, and reviewed evidence were
added to the distribution. **Mathematical sources, mapped inputs, build
configuration, dependency lockfile, integrity verifier, and reproduction script
were unchanged.** The final distribution manifest was regenerated and its
integrity checks rerun. The fresh logs' 125-file count refers to the tested
source export before the evidence/report additions; it is not the final
distribution's file count.

## Qualifications

The preliminary expanded candidate failed two obsolete required-dependency
assertions. Those failures were not relabeled as successes. Only the two
independently reviewed stale harnesses were omitted, with their original hashes
and current replacement coverage recorded; then this **complete final clean
reproduction** was run. See [SUPERSEDED_CHECKS.md](SUPERSEDED_CHECKS.md).

This result does not rerun historical cross-revision preservation against the
earlier baseline repository, nor certify complete correspondence with the latest
v19 manuscript. It does not certify illustrative numerical instances, simulation
implementations, practical extraction complexity, or a separate universal-machine
representation theorem for the host order-to-code compiler. The precise
mathematical and computational scope remains the one stated in the
[README](../README.md).
