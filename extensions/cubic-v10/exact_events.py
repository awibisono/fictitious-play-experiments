"""Exact installed simultaneous FP. Integer event jumps + independently certified RPS cycle batches.
No trajectory boundary or reset formula is used to move state.
A cycle batch is admitted only after every action's strict endpoint inequalities
are checked for every cycle index in the finite batch via exact quadratic minima.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from fractions import Fraction as F
from math import lcm, log10, isqrt, isfinite
from pathlib import Path
import json, sys, time, argparse, hashlib, gzip

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).parent


def require_integer(value, name, minimum):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def require_polynomial(p):
    if len(p) != 3 or any(type(x) is not int for x in p):
        raise ValueError("quadratic coefficients must be three exact integers")


def require_matrix(s, B):
    n = len(s)
    if n < 2 or len(B) != n or any(len(row) != n for row in B):
        raise ValueError("the matrix must be square and match the score vector")
    if any(type(x) is not int for row in B for x in row):
        raise ValueError("the payoff matrix must contain exact integers")


def load(k):
    require_integer(k, "order", 2)
    if k > 6:
        raise ValueError("installed order must be between 2 and 6")
    d = json.loads((ROOT / f"order{k}_construction.json").read_text())
    if type(d.get("order")) is not int or d["order"] != k:
        raise ValueError("construction order does not match the requested order")
    raw = d["matrix"]
    n = (k + 1) ** 2 - 5
    if len(raw) != n or any(len(row) != n for row in raw):
        raise ValueError("installed matrix has the wrong dimensions")
    if any(type(x) not in (str, int) for row in raw for x in row):
        raise ValueError("matrix entries must be exact rational strings or integers")
    digest = hashlib.sha256(json.dumps(raw, separators=(",", ":")).encode()).hexdigest()
    if d.get("matrix_sha256") != digest:
        raise ValueError("construction matrix SHA256 mismatch")
    A = [[F(x) for x in row] for row in raw]
    if any(A[i][j] != -A[j][i] for i in range(n) for j in range(n)):
        raise ValueError("installed matrix must be skew-symmetric")
    Q = F(d["Q"])
    if Q.denominator != 1 or Q <= 0:
        raise ValueError("Q must be a positive integer")
    D = lcm(*(x.denominator for row in A for x in row))
    B = [[int(x * D) for x in row] for row in A]
    return d, D, B


def decision(s):
    if not s or any(type(x) is not int for x in s):
        raise ValueError("scores must be a nonempty exact integer vector")
    h = max(s)
    ids = [i for i, x in enumerate(s) if x == h]
    if len(ids) != 1 or ids[0] == 0:
        raise ValueError("a unique non-setup best response is required")
    return ids[0]


def run(s, B):
    a = decision(s)
    if len(B) != len(s) or any(len(row) != len(s) for row in B):
        raise ValueError("the matrix must be square and match the score vector")
    if any(type(row[a]) is not int for row in B):
        raise ValueError("the active payoff column must contain exact integers")
    if B[a][a] != 0:
        raise ValueError("the active action diagonal must be zero")
    limits = [
        (s[a] - s[j] + B[j][a] - 1) // B[j][a] for j in range(len(s)) if B[j][a] > 0
    ]
    if not limits:
        raise ValueError("the current strict run has no finite endpoint")
    ell = min(limits)
    assert ell > 0
    assert all(s[a] - s[j] - (ell - 1) * B[j][a] > 0 for j in range(len(s)) if j != a)
    return a, ell


def polymin(p, u):
    require_polynomial(p)
    require_integer(u, "last index", 0)
    c, b, a = p
    v = min(c, c + b * u + a * u * u)
    if a > 0 and b < 0:
        r = (-b) // (2 * a)
        for x in (max(0, min(u, r)), max(0, min(u, r + 1))):
            v = min(v, c + b * x + a * x * x)
    return v


def first_nonpositive(p):
    """First integer r>=0 with c+b*r+a*r*r<=0, or None. Requires c>0."""
    require_polynomial(p)
    c, b, a = p
    if c <= 0:
        raise ValueError("the initial polynomial value must be positive")
    if a == 0:
        return (c - b - 1) // (-b) if b < 0 else None
    if a > 0 and (b >= 0 or b * b < 4 * a * c):
        return None
    disc = b * b - 4 * a * c
    root = isqrt(disc)
    if a < 0:
        r = max(0, (b + root) // (-2 * a))
        while c + b * r + a * r * r > 0:
            r += 1
        while r > 0 and c + b * (r - 1) + a * (r - 1) * (r - 1) <= 0:
            r -= 1
        return r
    r = max(0, (-b - root) // (2 * a))
    if c + b * r + a * r * r > 0:
        r += 1
    return r if c + b * r + a * r * r <= 0 else None


def cycle_batch(s, B, cap):
    require_integer(cap, "cycle cap", 1)
    if decision(s) != 1:
        return None
    if len(s) < 4:
        raise ValueError("an RPS batch needs setup and three active actions")
    n = len(s)
    st = s[:]
    lens = []
    for a in (1, 2, 3):
        aa, ll = run(st, B)
        if aa != a:
            return None
        lens.append(ll)
        st = [st[j] + ll * B[j][a] for j in range(n)]
    d0 = [st[j] - s[j] for j in range(n)]
    d1 = [3 * sum(B[j][a] for a in (1, 2, 3)) for j in range(n)]
    scorepoly = [[2 * s[j], 2 * d0[j] - d1[j], d1[j]] for j in range(n)]
    cert = []
    for a, ll in zip((1, 2, 3), lens):
        for last in (False, True):
            off = ll - 1 if last else 0
            slope = 3 if last else 0
            ss = [
                [p[0] + 2 * off * B[j][a], p[1] + 2 * slope * B[j][a], p[2]]
                for j, p in enumerate(scorepoly)
            ]
            for j in range(n):
                if j != a:
                    cert.append([ss[a][r] - ss[j][r] for r in range(3)])
        scorepoly = [
            [p[0] + 2 * ll * B[j][a], p[1] + 6 * B[j][a], p[2]]
            for j, p in enumerate(scorepoly)
        ]

    def valid(N):
        return all(polymin(p, N - 1) > 0 for p in cert)

    assert valid(1)
    failures = [r for p in cert if (r := first_nonpositive(p)) is not None]
    N = min([cap] + failures)
    assert valid(N)
    delta = [N * d0[j] + N * (N - 1) // 2 * d1[j] for j in range(n)]
    counts = {a: N * ll + 3 * N * (N - 1) // 2 for a, ll in zip((1, 2, 3), lens)}
    return N, delta, counts, len(cert), lens


def stepwise(s, B, T):
    require_integer(T, "rounds", 0)
    require_matrix(s, B)
    z = s[:]
    counts = [0] * len(s)
    for _ in range(T):
        a = decision(z)
        z = [x + B[j][a] for j, x in enumerate(z)]
        counts[a] += 1
    return z, counts


def jump_to(s, B, T):
    require_integer(T, "rounds", 0)
    require_matrix(s, B)
    z = s[:]
    counts = [0] * len(s)
    left = T
    while left:
        a, ll = run(z, B)
        ll = min(ll, left)
        z = [x + ll * B[j][a] for j, x in enumerate(z)]
        counts[a] += ll
        left -= ll
    return z, counts


def logint(n):
    require_integer(n, "logarithm argument", 1)
    return (
        log10(n)
        if n.bit_length() < 1000
        else log10(n >> (n.bit_length() - 100)) + (n.bit_length() - 100) * log10(2)
    )


def execute(k, eventlimit, seconds, target_logt, basebatch=True, publication_v5=False):
    require_integer(eventlimit, "event limit", 1)
    for name, value in (("seconds", seconds), ("target log time", target_logt)):
        if type(value) not in (int, float) or not isfinite(value) or value <= 0:
            raise ValueError(f"{name} must be positive and finite")
    if type(basebatch) is not bool or type(publication_v5) is not bool:
        raise ValueError("batching options must be booleans")
    data, D, B = load(k)
    n = len(B)
    s = [row[0] for row in B]
    counts = [1] + [0] * (n - 1)
    t = 1
    start = time.monotonic()
    batches = 0
    cycles = 0
    represented_runs = 0
    tests = 0
    endchecks = 0
    samples = []
    logs = []
    norm = max(abs(x) for row in B for x in row)

    def savepoint(event, kind):
        H = max(s)
        samples.append(
            dict(
                event=event,
                kind=kind,
                t=str(t),
                height_scaled=str(H),
                gap=str(F(2 * H, D * t)),
                normalized_gap=str(F(2 * H, norm * t)),
                log10_t=logint(t),
                log10_gap=logint(2 * H) - logint(D) - logint(t),
                log10_normalized_gap=logint(2 * H) - logint(norm) - logint(t),
            )
        )

    savepoint(0, "setup")
    for event in range(eventlimit):
        if event < 12 or event % 10000 == 0:
            assert stepwise(s, B, 256) == jump_to(s, B, 256)
            tests += 256
        cap = max(2, isqrt(sum(counts[1:])) // 100 + 1) if k == 2 else 2**20000
        if publication_v5 and k == 2:
            cap = min(cap, 2**40)
        batch = cycle_batch(s, B, cap) if basebatch else None
        if batch and batch[0] >= 2:
            N, delta, cc, checks, ll = batch
            # Independent event replay on first 10 and selected subsequent cycle-batch starts.
            if batches < 10 or batches % 1000 == 0:
                small = cycle_batch(s, B, min(7, N))
                NN, dd, ccc, _, _ = small
                ss = s[:]
                c2 = [0] * n
                for _ in range(3 * NN):
                    aa, l = run(ss, B)
                    c2[aa] += l
                    ss = [x + l * B[j][aa] for j, x in enumerate(ss)]
                assert ss == [s[j] + dd[j] for j in range(n)] and all(
                    c2[j] == ccc.get(j, 0) for j in range(n)
                )
            s = [s[j] + delta[j] for j in range(n)]
            for a, c in cc.items():
                counts[a] += c
            length = sum(cc.values())
            t += length
            batches += 1
            cycles += N
            represented_runs += 3 * N
            endchecks += checks
            logs.append(
                dict(
                    event=event,
                    t=str(t),
                    kind="RPS_cycle_batch",
                    cycles=str(N),
                    first_lengths=[str(x) for x in ll],
                    strict_quadratic_inequalities=checks,
                )
            )
        else:
            a, length = run(s, B)
            s = [x + length * B[j][a] for j, x in enumerate(s)]
            counts[a] += length
            t += length
            represented_runs += 1
            endchecks += 2 * (n - 1)
            logs.append(
                dict(
                    event=event,
                    t=str(t),
                    kind="maximal_constant_action",
                    action=a,
                    length=str(length),
                )
            )
        sample_stride = 10 if publication_v5 and k == 2 else 100
        if event < 128 or event % sample_stride == 0:
            savepoint(event + 1, logs[-1]["kind"])
        if event % 10000 == 0:
            print(
                "PROGRESS",
                k,
                event,
                "log10t",
                round(logint(t), 4),
                "basecycles",
                cycles,
                "seconds",
                round(time.monotonic() - start, 2),
                flush=True,
            )
        if logint(t) >= target_logt or time.monotonic() - start >= seconds:
            break
    savepoint(event + 1, "final")
    assert sum(counts) == t
    assert s == [sum(B[i][j] * counts[j] for j in range(n)) for i in range(n)]
    result = dict(
        order=k,
        method="Exact maximal constant-action jumps; optional exact finite quadratic-inequality RPS cycle certification",
        matrix_sha256=data["matrix_sha256"],
        Q=data["Q"],
        integer_scale=str(D),
        integer_scale_bits=D.bit_length(),
        normalization_max_scaled=str(norm),
        normalization="A / max_ij(abs(A_ij)); original trajectory unchanged",
        t_convention="Completed simultaneous rounds including prescribed common setup move at t=1; both empirical counts identical",
        events=event + 1,
        represented_constant_action_runs=str(represented_runs),
        certified_base_cycle_batches=batches,
        certified_base_cycles=str(cycles),
        strict_endpoint_polynomial_checks=endchecks,
        stepwise_comparison_updates=tests,
        t=str(t),
        counts=[str(x) for x in counts],
        final_scores_scaled=[str(x) for x in s],
        wall_seconds=time.monotonic() - start,
        samples=samples,
    )
    path = ROOT / f"order{k}_event_result.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    with gzip.open(ROOT / f"order{k}_event_transcript.jsonl.gz", "wt") as f:
        for rec in logs:
            f.write(json.dumps(rec, separators=(",", ":")) + "\n")
    print(
        "DONE",
        k,
        "events",
        event + 1,
        "log10t",
        logint(t),
        "runs",
        represented_runs,
        "seconds",
        result["wall_seconds"],
        flush=True,
    )
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--orders", nargs="+", type=int, default=[2, 3, 4, 5])
    ap.add_argument("--events", type=int, default=100000)
    ap.add_argument("--seconds", type=float, default=120)
    ap.add_argument("--logt", type=float, default=1000)
    ap.add_argument("--no-cycle-batch", action="store_true")
    ap.add_argument(
        "--publication-v5",
        action="store_true",
        help="Reproduce archived order-two cap and sampling cadence",
    )
    a = ap.parse_args()
    for k in a.orders:
        execute(k, a.events, a.seconds, a.logt, not a.no_cycle_batch, a.publication_v5)
