if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, time, hashlib
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import certify_recursive_word as c

H = Path(__file__).parent
replay = json.loads((H / "order6_recursive_replay.json").read_text())
assert replay["status"] == "PASS"
m = c.model(6)
Q = m["Q"]
D = m["D"]
B = m["B"]
norm = max(abs(x) for row in B for x in row)
cp = F(m["data"]["rate_constant_power_k"])
records = []
for q in [Q, Q + 1] + [Q * 2**j for j in range(1, 13)]:
    assert Q <= q <= int(replay["final_q"])
    inc, state = c.endpoint(m, q - Q)
    counts = [1] + inc
    t = sum(counts)
    h = max(state)
    gap = F(2 * h, D * t)
    assert state == [
        sum(B[i][j] * counts[j] for j in range(len(B))) for i in range(len(B))
    ]
    with localcontext() as ctx:
        ctx.prec = 95
        dd = lambda x: Decimal(x.numerator) / Decimal(x.denominator)
        p = dict(
            q=str(q),
            t=str(t),
            gap=str(gap),
            normalized_gap=str(F(2 * h, norm * t)),
            height_scaled=str(h),
            log10_t=str(Decimal(t).log10()),
            log10_normalized_gap=str(dd(F(2 * h, norm * t)).log10()),
            ratio_to_asymptote=str(
                dd(gap) * Decimal(t) ** (Decimal(1) / 6) / (dd(cp) ** (Decimal(1) / 6))
            ),
        )
        if records:
            p["previous_secant"] = str(
                dd(gap / F(records[-1]["gap"])).ln()
                / (Decimal(t) / Decimal(records[-1]["t"])).ln()
            )
    records.append(p)
result = dict(
    order=6,
    status="PASS",
    method="Exact internal prefix extraction from an already fully certified finite word, using derived word counts and actual B; no new trajectory theorem assumption",
    coverage_source="order6_recursive_replay.json",
    coverage_source_sha256=hashlib.sha256(
        (H / "order6_recursive_replay.json").read_bytes()
    ).hexdigest(),
    engine_sha256=hashlib.sha256(Path(c.__file__).read_bytes()).hexdigest(),
    Q=str(Q),
    samples=records,
)
(H / "order6_dense_certified_samples.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print(
    "PASS dense sextic samples",
    len(records),
    "last secant",
    records[-1]["previous_secant"],
    flush=True,
)
