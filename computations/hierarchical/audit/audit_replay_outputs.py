"""Check saved finite replay states, gaps, times and limiting constants using only word sums."""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, hashlib, time
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import independent_general_certificate as ind


def run(k, res_override=None):
    m = ind.build(k)
    B = m["B"]
    D = m["D"]
    dim = len(B)
    Q = m["Q"]
    respath = HERE.parent / f"order{k}_recursive_replay.json"
    res = json.loads(respath.read_text()) if res_override is None else res_override
    assert int(res["integer_scale"]) == D
    norm = max(abs(x) for r in B for x in r)
    assert int(res["normalization_max_scaled"]) == norm
    S = {a: ind.sum_shifted(p, ind.c(0), ind.var(0)) for a, p in m["topcounts"].items()}
    T = ind.add(ind.c(1), ind.summ(S.values()))
    leadT = T[(k,) + (0,) * (k - 2)]
    highcoeff = (k - 1,) + (0,) * (k - 2)
    leadH = max(p.get(highcoeff, F(0)) for p in m["entry"][1:])
    assert all(max((e[0] for e in p), default=0) <= k - 1 for p in m["entry"][1:])
    assert m["entry"][0].get((k,) + (0,) * (k - 2), F(0)) < 0
    cp = F(2 * leadH, D) ** k / leadT ** (k - 1)
    raw = json.loads((HERE.parents[1] / f"order{k}_construction.json").read_text())
    assert cp == F(raw["rate_constant_power_k"])
    max_ratio_error = Decimal(0)
    max_secant_error = Decimal(0)
    prev = None
    for rec in res["samples"]:
        q = int(rec["q"])
        P = q - Q
        args = (P,) + (0,) * (k - 2)
        counts = [1] + [int(ind.at(S.get(a, {}), args)) for a in range(1, dim)]
        scores = [int(ind.at(p, args)) for p in m["entry"]]
        assert scores == [
            sum(B[i][a] * counts[a] for a in range(dim)) for i in range(dim)
        ]
        t = sum(counts)
        H = max(scores)
        assert str(t) == rec["t"] and str(H) == rec["height_scaled"]
        gap = F(2 * H, D * t)
        assert gap == F(rec["gap"]) and F(2 * H, norm * t) == F(rec["normalized_gap"])
        with localcontext() as ctx:
            ctx.prec = 110
            dec = lambda x: Decimal(x.numerator) / Decimal(x.denominator)
            ratio = (
                dec(gap) * Decimal(t) ** (Decimal(1) / k) / dec(cp) ** (Decimal(1) / k)
            )
            err = abs(ratio - Decimal(rec["ratio_to_asymptote"]))
            assert err / max(Decimal(1), abs(ratio)) < Decimal("1e-75")
            max_ratio_error = max(max_ratio_error, err / max(Decimal(1), abs(ratio)))
            if prev:
                sec = (dec(gap / prev[1])).ln() / (Decimal(t) / Decimal(prev[0])).ln()
                err = abs(sec - Decimal(rec["previous_secant"]))
                assert err < Decimal("1e-70")
                max_secant_error = max(max_secant_error, err)
            prev = (t, gap)
    if str(q) == res["final_q"]:
        assert [str(x) for x in counts] == res["counts"] and [
            str(x) for x in scores
        ] == res["final_scores_scaled"]
    return dict(
        order=k,
        status="PASS",
        samples_checked=len(res["samples"]),
        final_q=res["final_q"],
        completed_phases=res["completed_outer_phases"],
        final_log10_t=res["samples"][-1]["log10_t"],
        final_ratio=res["samples"][-1]["ratio_to_asymptote"],
        final_secant=res["samples"][-1]["previous_secant"],
        limiting_constant_independently_rederived=True,
        largest_relative_decimal_ratio_error=str(max_ratio_error),
        largest_decimal_secant_error=str(max_secant_error),
        replay_file_sha256=hashlib.sha256(respath.read_bytes()).hexdigest(),
    )


if __name__ == "__main__":
    tick = time.monotonic()
    out = [run(k) for k in (4, 5)]
    result = dict(results=out, seconds=time.monotonic() - tick)
    (HERE / "replay_output_audit_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))
