# Current v19 central correspondence review

**No discrepancy found in the checked central scope.** On 2 November 2026, the
central mathematical statements and computational qualifications were compared
against source-bound verbatim extracts of the current v19 manuscript and the
audited Lean source. Relevant release source files were reread, including the
arbitrary-fixed-start-phase result.

This is **not** a renewed whole-manuscript proof audit or a refreshed complete
statement-by-statement crosswalk. The historical full audit reference and the
fresh Lean build identity remain unchanged.

## Reference identity

- Manuscript source file: `master_v19_v2.tex`.
- Manuscript source revision:
  `ffc8a40843adb2adafc1cbcc827cfe6df7a52496`.
- Full manuscript source SHA-256:
  `b487c7cc70439ccaef9ba4884222f4b03176a8b556c774c3681ec9f62932ec3e`.
- Audited Lean upstream revision:
  `23f53ae238d01b1be52c981434c6abaef5cd49c9`.

The manuscript line references below belong to this exact v19 source. The
review used the specified extracts; the full-file hash identifies their source
and does not mean that every manuscript proof was independently reviewed.

## Checked clauses

| Manuscript clause | Lean correspondence and finding |
| --- | --- |
| Main theorem, lines 307–318 | `FaithfulMain.main_theorem` has `k ≥ 2`, rational skew games, `(k+1)^2−5` actions, zero initial counts and setup action 0, simultaneous unique responses after setup, and the stated rate. It adds no external clock-validity or asymptotic premise. |
| Smaller family, lines 365–367 | `FaithfulSevenFamily.main_theorem` has `k ≥ 3`, `(k+1)^2−9` actions, and the corresponding strict-play and rate properties. |
| Fictitious play and gap definitions, lines 242–290 | `UnrolledTrajectory` uses pre-round cumulative counts, simultaneous row maximization and column minimization, and the actual empirical max-minus-min gap. |
| Setup construction, lines 1220–1231 | `FaithfulProcessSetup` implements the minimum shift, one added action that is not replayed, and strict simulation and uniqueness. |
| All-time statement, lines 1236–1250 and its extracted proof statement | `FaithfulRate`, `FaithfulRealization`, and `FaithfulStartPhase` give the same positive constant `c = 2[ξ/(k−1)!][L/k!]^(-(k−1)/k)`, count the setup action, establish the all-integer-time relative `O(t^(-1/k))` error, and allow every fixed `Q ≥ Qk` with the same constant. |
| Threshold and computational qualifications, line 1054, lines 1076–1082, and Section 8 lines 2501–2502 | `FaithfulClock` and `FaithfulEffectiveContract` distinguish raw `Clock` from a verified realizer for generic computational claims. Both families supply realizers. One code is chosen before all positive inputs; terminating fuel may depend on the input. The code computes the actual inherited threshold with the stated prefix guarantee. |

The start-phase source file has SHA-256
`2b15326a489bf6a1fb4f7e02a284d4a05aa663f727d5553cd0aa867449e885f3`.
The other retained mathematical source identities are recorded in
[`../provenance/SOURCE_MAP.json`](../provenance/SOURCE_MAP.json).

## Limits and unchanged build provenance

This review does not cover all unextracted v19 proofs, the literature or
optimality comparisons, every displayed numerical matrix, or the experiments.
It does not establish practical runtime or bit complexity, or add a separate
universal-machine representation theorem for the host order-to-code compiler.

No Lean source, proof, dependency, verifier, or reproduction script was changed
for this correspondence update. The completed clean build and its six
independent probes and eight companion checks remain the run documented in
[`FRESH_VERIFICATION.md`](FRESH_VERIFICATION.md). Only release documentation,
reference metadata, status, and the distribution manifest were updated.
