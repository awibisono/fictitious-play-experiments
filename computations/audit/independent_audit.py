"""Independent finite-step and polynomial certificate audit; writes only audit/.
The oracle computes both players' pre-round best responses independently.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, random, hashlib, time

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction as F
from math import lcm

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import exact_events as candidate

OUT = Path(__file__).resolve().parent
rng = random.Random(7819571)


def unique_argmax(v):
    m = max(v)
    ids = [i for i, x in enumerate(v) if x == m]
    assert len(ids) == 1, ("tie", ids)
    return ids[0]


def direct_round(s, B):
    # With synchronized empirical counts and skew symmetry, row score is s;
    # column player's minimization score is -s. Both select before updating.
    r = unique_argmax(s)
    col_scores = [-v for v in s]
    c = min(range(len(s)), key=col_scores.__getitem__)
    assert sum(x == col_scores[c] for x in col_scores) == 1 and r == c
    return [s[i] + B[i][c] for i in range(len(s))], r


def oracle_run(s, B):
    a = unique_argmax(s)
    limits = []
    for j in range(len(s)):
        if j == a:
            continue
        gap = s[a] - s[j]
        loss = B[j][a] - B[a][a]
        assert gap > 0
        if loss > 0:
            q, r = divmod(gap, loss)
            limits.append(q + (r != 0))
    L = min(limits)
    return a, L


def add_counts(s, B, c):
    return [s[i] + sum(B[i][j] * v for j, v in c.items()) for i in range(len(s))]


def candidate_cycle_start(s, B, lengths, h):
    c = {a: h * lengths[a - 1] + 3 * h * (h - 1) // 2 for a in (1, 2, 3)}
    return add_counts(s, B, c)


def scores_at(s, B, lengths, h, a, last):
    z = candidate_cycle_start(s, B, lengths, h)
    for b in range(1, a):
        z = add_counts(z, B, {b: lengths[b - 1] + 3 * h})
    if last:
        z = add_counts(z, B, {a: lengths[a - 1] + 3 * h - 1})
    return z


def quadratic_min_from_three(values, last_index):
    # Newton finite differences avoid reusing the runner's score coefficients.
    f0, f1, f2 = values
    d1 = f1 - f0
    d2 = f2 - 2 * f1 + f0

    def f(h):
        return f0 + h * d1 + h * (h - 1) // 2 * d2

    points = {0, last_index}
    if d2 > 0:
        vertex = F(d2 - 2 * d1, 2 * d2)
        left = vertex.numerator // vertex.denominator
        points.update(max(0, min(last_index, p)) for p in (left, left + 1))
    return min((f(h), h) for h in points)


def audit_batch(s, B, batch, cap, stats):
    N, delta, counts, checks, lengths = batch
    n = len(s)
    assert 1 <= N <= cap and len(lengths) == 3 and all(x > 0 for x in lengths)
    assert checks == 6 * (n - 1)
    assert counts == {a: N * lengths[a - 1] + 3 * N * (N - 1) // 2 for a in (1, 2, 3)}
    assert add_counts(s, B, counts) == [x + y for x, y in zip(s, delta)]
    records = []
    for a in (1, 2, 3):
        for last in (False, True):
            z = [scores_at(s, B, lengths, h, a, last) for h in (0, 1, 2)]
            for j in range(n):
                if j == a:
                    continue
                vals = [zz[a] - zz[j] for zz in z]
                v, h = quadratic_min_from_three(vals, N - 1)
                assert v > 0, ("unsafe certificate", a, last, j, N, h, v)
                records.append(vals)
    if N < cap:
        assert any(quadratic_min_from_three(v, N)[0] <= 0 for v in records), (
            "nonmaximal batch",
            N,
            cap,
        )
        stats["certified_rejection_boundaries"] += 1
    stats["independent_exact_polynomial_minima"] += len(records)
    # Finite windows at the start and end of all run types across first/middle/last
    # cycles, checking both simultaneous choices at every directly tested round.
    for h in sorted({0, N // 2, N - 1}):
        for a in (1, 2, 3):
            L = lengths[a - 1] + 3 * h
            for off in sorted({0, max(0, L - 8)}):
                z = scores_at(s, B, lengths, h, a, False)
                z = add_counts(z, B, {a: off})
                for step in range(min(8, L - off)):
                    z, played = direct_round(z, B)
                    assert played == a, ("stepwise batch mismatch", h, a, off, step)
                    stats["direct_rounds"] += 1
            z = scores_at(s, B, lengths, h, a, True)
            z, played = direct_round(z, B)
            expected = a + 1 if a < 3 else 1 if h + 1 < N else None
            actual = unique_argmax(z)
            if expected is not None:
                assert actual == expected
            stats["direct_batch_switches"] += 1
    stats["batches"] += 1


def audit_order(k, maxevents):
    data = json.loads((ROOT / f"order{k}_construction.json").read_text())
    A = [[F(v) for v in row] for row in data["matrix"]]
    n = len(A)
    D = lcm(*(v.denominator for row in A for v in row))
    B = [[int(v * D) for v in row] for row in A]
    assert all(B[i][j] == -B[j][i] for i in range(n) for j in range(n))
    assert all(B[i][i] == 0 for i in range(n))
    assert (
        hashlib.sha256(
            json.dumps(data["matrix"], separators=(",", ":")).encode()
        ).hexdigest()
        == data["matrix_sha256"]
    )
    assert all(B[0][j] < 0 for j in range(1, n))
    stats = dict(
        order=k,
        dimension=n,
        events=0,
        batches=0,
        direct_rounds=0,
        direct_batch_switches=0,
        direct_event_switches=0,
        independent_exact_polynomial_minima=0,
        certified_rejection_boundaries=0,
        actions_seen=set(),
        first_actions=[],
        first_batch_lengths=None,
        completed_outer_entry_returns=0,
    )
    s = [row[0] for row in B]
    counts = [1] + [0] * (n - 1)
    t = 1
    # A fully independent exact simultaneous prefix. On high orders, this prefix
    # lies in an enormous controller plateau; boundary windows below cover switches.
    ss = s[:]
    for step in range(512):
        ss, a = direct_round(ss, B)
        stats["direct_rounds"] += 1
    assert candidate.stepwise(s, B, 512)[0] == ss
    for e in range(maxevents):
        a, L = oracle_run(s, B)
        assert (a, L) == candidate.run(s, B)
        stats["actions_seen"].add(a)
        if len(stats["first_actions"]) < 80:
            stats["first_actions"].append(a)
        cap = 2**40 if e % 4 else (e % 17 + 1)
        batch = candidate.cycle_batch(s, B, cap)
        if batch is not None:
            audit_batch(s, B, batch, cap, stats)
            if stats["first_batch_lengths"] is None:
                stats["first_batch_lengths"] = [str(x) for x in batch[-1]]
        if batch and batch[0] >= 2:
            N, delta, cc, checks, lengths = batch
            s = add_counts(s, B, cc)
            for a, v in cc.items():
                counts[a] += v
            t += sum(cc.values())
        else:
            # Independently simulate the last eight rounds and eight following
            # rounds around every event boundary, not merely an initial plateau.
            skip = max(0, L - 8)
            near = add_counts(s, B, {a: skip})
            for ii in range(L - skip):
                near, aa = direct_round(near, B)
                assert aa == a
                stats["direct_rounds"] += 1
            end = add_counts(s, B, {a: L})
            assert end == near
            assert unique_argmax(end) != a
            stats["direct_event_switches"] += 1
            after = end[:]
            for ii in range(8):
                after, aa = direct_round(after, B)
                stats["direct_rounds"] += 1
            assert after == candidate.jump_to(end, B, 8)[0]
            s = end
            counts[a] += L
            t += L
        # Verify scores straight from cumulative action counts.
        assert sum(counts) == t
        assert s == [sum(B[i][j] * counts[j] for j in range(n)) for i in range(n)]
        # Direct general gap formula verifies sign, denominator, and normalization.
        y = [F(c, t) for c in counts]
        if e < 10 or e % 50 == 0:
            row = [sum(A[i][j] * y[j] for j in range(n)) for i in range(n)]
            col = [sum(A[i][j] * y[i] for i in range(n)) for j in range(n)]
            gap = max(row) - min(col)
            assert gap == F(2 * max(s), D * t)
            norm = max(abs(v) for r in A for v in r)
            assert gap / norm == F(2 * max(s), max(abs(v) for r in B for v in r) * t)
        stats["events"] += 1
    stats["actions_seen"] = sorted(stats["actions_seen"])
    stats["final_t"] = str(t)
    return stats


def test_polymin():
    for trial in range(50000):
        p = [rng.randint(-10000, 10000) for _ in range(3)]
        u = rng.randrange(101)
        expected = min(p[0] + p[1] * j + p[2] * j * j for j in range(u + 1))
        assert candidate.polymin(p, u) == expected, (p, u)
    # Large-integer vertices and near-zero strict inequalities.
    for power in range(1, 101):
        v = 10**power + 3
        for eps in (-1, 0, 1):
            p = [v * v + eps, -2 * v, 1]
            assert candidate.polymin(p, 2 * v) == eps
    return 50300


if __name__ == "__main__":
    start = time.monotonic()
    results = {"polymin_cases": test_polymin(), "orders": []}
    for k, maxevents in [(2, 200), (3, 1000), (4, 1000), (5, 1000)]:
        result = audit_order(k, maxevents)
        results["orders"].append(result)
        print(json.dumps(result), flush=True)
        (OUT / "independent_audit_results.json").write_text(
            json.dumps(results, indent=2) + "\n"
        )
    results["seconds"] = time.monotonic() - start
    (OUT / "independent_audit_results.json").write_text(
        json.dumps(results, indent=2) + "\n"
    )
    print("PASS", results["seconds"], flush=True)
