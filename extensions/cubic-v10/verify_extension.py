"""Independent read-only arithmetic checks of saved transcript, states and ratios."""

import json, gzip, math, hashlib
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext

if not __debug__:
    raise RuntimeError("Run verification without -O or -OO")
R = Path(__file__).resolve().parent
old = R.parents[1] / "computations"
d = json.loads((R / "order3_event_result.json").read_text())
c = json.loads((R / "order3_construction.json").read_text())
o = json.loads((old / "order3_event_result.json").read_text())
scale = int(d["integer_scale"])
B = [[int(F(x) * scale) for x in row] for row in c["matrix"]]
norm = max(abs(x) for row in B for x in row)
assert d["events"] == 2000000 and d["wall_seconds"] < 300 and int(d["t"]) < 10**1000
assert (R / "exact_events.py").read_bytes() == (old / "exact_events.py").read_bytes()
assert (R / "order3_construction.json").read_bytes() == (
    old / "order3_construction.json"
).read_bytes()
counts = [1] + [0] * 10
t = 1
maxbatch = 0
batches = cycles = runs = 0
samples = {s["event"]: s for s in d["samples"]}


def check_sample(event):
    s = samples[event]
    scores = [sum(a * b for a, b in zip(row, counts)) for row in B]
    H = max(scores)
    assert int(s["t"]) == t and int(s["height_scaled"]) == H
    assert F(s["gap"]) == F(2 * H, scale * t) and F(s["normalized_gap"]) == F(
        2 * H, norm * t
    )


check_sample(0)
with gzip.open(R / "order3_event_transcript.jsonl.gz", "rt") as f:
    for i, line in enumerate(f):
        rec = json.loads(line)
        assert rec["event"] == i
        if rec["kind"] == "RPS_cycle_batch":
            N = int(rec["cycles"])
            batches += 1
            cycles += N
            runs += 3 * N
            maxbatch = max(maxbatch, N)
            inc = [N * int(ll) + 3 * N * (N - 1) // 2 for ll in rec["first_lengths"]]
            for a, n in zip((1, 2, 3), inc):
                counts[a] += n
            t += sum(inc)
        else:
            n = int(rec["length"])
            counts[rec["action"]] += n
            t += n
            runs += 1
        assert t == int(rec["t"])
        if i + 1 in samples:
            check_sample(i + 1)
        if i + 1 == o["events"]:
            assert counts == list(map(int, o["counts"])) and t == int(o["t"])
assert (
    i + 1 == d["events"]
    and counts == list(map(int, d["counts"]))
    and sum(counts) == int(d["t"]) == t
)
assert [sum(a * b for a, b in zip(row, counts)) for row in B] == list(
    map(int, d["final_scores_scaled"])
)
assert (
    batches == d["certified_base_cycle_batches"]
    and cycles == int(d["certified_base_cycles"])
    and runs == int(d["represented_constant_action_runs"])
)
# Existing regular samples must be bit-for-bit preserved; old final is checked by counts above.
for s in o["samples"]:
    if s["kind"] != "final":
        assert samples[s["event"]] == s
Q = int(c["Q"])
phases = 250000
q = Q + phases
formula_counts = [F(1)] + [
    sum(F(row[j]) * (math.comb(q, j + 1) - math.comb(Q, j + 1)) for j in range(3))
    for row in c["C"]
]
assert formula_counts == counts
with localcontext() as ctx:
    ctx.prec = 85
    cp = F(c["rate_constant_power_k"])
    constant = (D(cp.numerator) / D(cp.denominator)) ** (D(1) / 3)

    def ratio(result):
        gap = F(result["samples"][-1]["gap"])
        return (
            D(gap.numerator)
            / D(gap.denominator)
            * D(result["t"]) ** (D(1) / 3)
            / constant
        )

    rr = ratio(d)
    ro = ratio(o)
    report = dict(
        status="PASS",
        termination="event budget",
        events=d["events"],
        t=d["t"],
        log10_t=str(D(t).log10()),
        completed_outer_phases=phases,
        final_phase=q,
        max_batch_cycles=maxbatch,
        represented_runs=str(runs),
        ratio=str(rr),
        relative_deviation=str(rr - 1),
        old_relative_deviation=str(ro - 1),
        deviation_reduction_factor=str((ro - 1) / (rr - 1)),
        samples_checked=len(d["samples"]),
        checks=[
            "unmodified audited engine and matrix",
            "every transcript event count/time update",
            "every saved sample score/gap/normalization",
            "full archived trajectory sample prefix and million-event state",
            "final count/score identities",
            "exact count-table boundary identity",
        ],
        limitation="Production event certificates cover all skipped decisions. Independent extension check reconstructs transcript counts and sample scores, but does not separately rederive every new decision inequality.",
        files={
            p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [
                R / "exact_events.py",
                R / "order3_construction.json",
                R / "order3_event_result.json",
                R / "order3_event_transcript.jsonl.gz",
            ]
        },
    )
(R / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
