# Alpha v10: exact cubic extension and revised figures

This isolated supplement leaves the 3 October audited release unchanged. It extends only the k=3 event simulation and replots the existing k=2,4,5,6 data. Figures were checked visually for clipping and label readability.

## Verified outcome

- 2,000,000 computational events, 250,000 completed outer phases; final phase 251733 from Q=1733
- Completed time 16727255004807900625001; log10(t)=22.223424677718157...
- Gap/(c3*t^(-1/3)) = 1.0000516384596625405...
- Relative deviation 5.16384596625405e-5, reduced by a factor 3.81117 from the earlier million-event endpoint
- 95,051,875,000 represented constant-action runs; largest certified RPS batch 251733 cycles
- Event budget caused termination. The simulation remained below the 300-second budget and log10(t)=1000 threshold
- 153.51 seconds of simulation; 178.64 seconds including serialization; 854272 KiB peak RSS (834.25 MiB), within a 2 GiB address-space limit

The deviation is finite-time disagreement with the leading asymptotic formula, not numerical trajectory error. The extension is a finite exact computation, not a new proof of infinite-time convergence.

## Reproduction

Python 3.11+ is sufficient for simulation and independent arithmetic verification. Do not run with -O. Copy exact_events.py and order3_construction.json to a new writable directory before running, because the engine writes alongside itself:

    python exact_events.py --orders 3 --events 2000000 --seconds 300 --logt 1000

The supplied run_bounded.py additionally imposes a 2 GiB address-space limit, an overall 420-second timeout and records resource usage. Time limits may terminate a run early on slower machines; verify that events equals 2000000 before comparing final values. The --publication-v5 switch has no effect for k=3; it is only needed for the original k=2 cap/sampling convention.

verify_extension.py independently reconstructs every transcript count/time update and every saved sample's scores, gap and normalization, checks the old million-event state and all old regular samples, and compares final counts with exact phase-count formulas. The baseline is resolved relative to this repository, so retain the directory layout. verification.json records checks and input/output SHA-256 hashes. The additional `verify_full_cubic.py` independently rederives every constant-run and batched-cycle decision inequality from payoff columns. `full-cubic-audit.json` records its successful full finite-horizon audit, including all 2,000,000 events and 95,051,875,000 represented runs. Run `python extensions/cubic-v10/verify_full_cubic.py` from the repository root to repeat it; this can take several minutes. All verification scripts must run without -O/-OO.

For figures, use the audited release's pinned Matplotlib environment:

    python replot_v10.py --data-root . --output-dir figures

All required plot inputs are included here. Figure 6 uses the existing v8 design, expands the k=2 onset x range from [0,6] to [0,8], and includes the extended cubic samples through log10(t)=22.2234. Dashed zero references identify the limiting log-ratio. Figure 7 retains all existing sampled gaps/errors, changes its right x coordinate from q/Q to log10(t), uses identical horizontal limits on the left and right of each row, and labels samples as phase starts. The plotted lines between samples are guides, not additional trajectory observations. 

The figure-generation script checks exact normalization identities for all plotted observations before converting to floating point for display. The audited base release's old plot-array fingerprints are intentionally not used as expected outputs for these revised figures. plot_report.json provides current sample counts and axis windows.

The compressed cubic transcript is stored as five byte-exact parts for reliable transfer. Before transcript verification, reconstruct it once:

```sh
python extensions/cubic-v10/assemble_transcript.py
```

This checks every part and the complete original SHA-256. The joined file is generated locally and ignored by Git.
