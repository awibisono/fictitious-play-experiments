if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, time, json, hashlib, argparse
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import certify_recursive_word as c

HERE = Path(__file__).parent


def execute(k, doublings):
    data, D, B = c.ee.load(k)
    Q = int(data["Q"])
    q = Q
    state = [row[0] for row in B]
    counts = [1] + [0] * (len(B) - 1)
    t = 1
    start = time.monotonic()
    records = []
    certs = []
    norm = max(abs(x) for row in B for x in row)
    cp = F(data["rate_constant_power_k"])

    def save():
        h = max(state)
        g = F(2 * h, D * t)
        with localcontext() as ctx:
            ctx.prec = 85
            dd = lambda x: Decimal(x.numerator) / Decimal(x.denominator)
            ratio = (
                dd(g) * Decimal(t) ** (Decimal(1) / k) / (dd(cp) ** (Decimal(1) / k))
            )
            p = dict(
                q=str(q),
                t=str(t),
                gap=str(g),
                normalized_gap=str(F(2 * h, norm * t)),
                height_scaled=str(h),
                log10_t=str(Decimal(t).log10()),
                log10_normalized_gap=str(dd(F(2 * h, norm * t)).log10()),
                ratio_to_asymptote=str(ratio),
            )
            if records:
                prev = records[-1]
                p["previous_secant"] = str(
                    (dd(g / F(prev["gap"]))).ln()
                    / (Decimal(t) / Decimal(prev["t"])).ln()
                )
        records.append(p)

    save()
    targets = [Q + 1] + [Q * 2**j for j in range(1, doublings + 1)]
    for endq in targets:
        m = c.model(k, initial=state, Q=q)
        P = endq - q
        result, _ = c.certify(m, P)
        if result["status"] != "PASS":
            raise AssertionError(result)
        inc, newstate = c.endpoint(m, P)
        for i, z in enumerate(inc, 1):
            counts[i] += z
        state = newstate
        t += sum(inc)
        q = endq
        assert t == sum(counts)
        assert state == [
            sum(B[i][j] * counts[j] for j in range(len(B))) for i in range(len(B))
        ]
        # This is post-certification cross-check only; it never selects actions.
        for i, row in enumerate(data["R"]):
            expected = c.evalrow(row, q) - c.evalrow(row, Q) + F(B[i + 1][0], D)
            assert F(state[i + 1], D) == expected
        certs.append(result)
        save()
        print(
            "CERTIFIED",
            k,
            "q/Q",
            F(q, Q),
            "logt",
            records[-1]["log10_t"][:16],
            "ratio",
            records[-1]["ratio_to_asymptote"][:24],
            "seconds",
            round(time.monotonic() - start, 2),
            flush=True,
        )
    result = dict(
        status="PASS",
        method="Sequential exact finite-word certificate; every skipped decision checked by tensor Bernstein positivity against every installed action",
        order=k,
        actions=len(B),
        Q=str(Q),
        final_q=str(q),
        completed_outer_phases=str(q - Q),
        t=str(t),
        counts=[str(x) for x in counts],
        final_scores_scaled=[str(x) for x in state],
        integer_scale=str(D),
        normalization_max_scaled=str(norm),
        matrix_sha256=data["matrix_sha256"],
        engine_sha256=hashlib.sha256(Path(c.__file__).read_bytes()).hexdigest(),
        certificates=certs,
        samples=records,
        elapsed_seconds=time.monotonic() - start,
        independent_boundary_formula_crosscheck=True,
    )
    (HERE / f"order{k}_recursive_replay.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--orders", type=int, nargs="+", default=[4])
    p.add_argument("--doublings", type=int, default=12)
    a = p.parse_args()
    for k in a.orders:
        execute(k, a.doublings)
