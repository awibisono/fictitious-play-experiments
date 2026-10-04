"""Repeat independent full-horizon certificate signs and validate saved actual states."""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from pathlib import Path
from fractions import Fraction as F
import sys, json, time, hashlib

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
root = Path(__file__).resolve().parents[1] / "hierarchical"
sys.path.insert(0, str(root / "audit"))
import independent_general_certificate as ind

results = []
for k in (4, 5):
    tick = time.monotonic()
    d = json.loads((root / f"order{k}_recursive_replay.json").read_text())
    m = ind.build(k)
    P = int(d["completed_outer_phases"])
    subs = ind.flatten(m, P)
    failures = []
    ncoeff = 0
    for tag, p, strict in m["cert"]:
        coeff, degrees = ind.bernstein(ind.compose(p, subs))
        ncoeff += len(coeff)
        lower = min(coeff.values())
        if lower < 0 or (strict and lower <= 0):
            failures.append(tag)
    B = m["B"]
    D = m["D"]
    counts = [int(x) for x in d["counts"]]
    scores = [sum(B[i][a] * counts[a] for a in range(len(B))) for i in range(len(B))]
    assert scores == [int(x) for x in d["final_scores_scaled"]]
    assert counts[0] == 1 and sum(counts) == int(d["t"])
    last = d["samples"][-1]
    H = max(scores)
    t = sum(counts)
    norm = max(abs(x) for row in B for x in row)
    assert F(last["gap"]) == F(2 * H, D * t)
    assert F(last["normalized_gap"]) == F(2 * H, norm * t)
    assert int(d["final_q"]) - int(d["Q"]) == P
    assert int(d["final_q"]) == 4096 * int(d["Q"])
    assert all(c["status"] == "PASS" for c in d["certificates"])
    assert sum(int(c["phases"]) for c in d["certificates"]) == P
    assert not failures
    results.append(
        {
            "order": k,
            "status": "PASS",
            "independent_inequalities": len(m["cert"]),
            "independent_direct_Bernstein_coefficients": ncoeff,
            "completed_phases": str(P),
            "actual_state_count_time_gap_checks": "PASS",
            "replay_sha256": hashlib.sha256(
                (root / f"order{k}_recursive_replay.json").read_bytes()
            ).hexdigest(),
            "seconds": time.monotonic() - tick,
        }
    )
    print(json.dumps(results[-1]), flush=True)
Path(__file__).with_name("hierarchical_sign_recheck.json").write_text(
    json.dumps(results, indent=2) + "\n"
)
