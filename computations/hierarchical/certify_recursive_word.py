"""Exact finite-word fictitious-play certification.
M/stride tables propose a word. Every skipped best response is separately
certified against every installed action by exact tensor Bernstein positivity.
Phase count polynomials are independently summed from that proposed word.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, time, math, itertools, hashlib
from fractions import Fraction as F
from pathlib import Path

sys.set_int_max_str_digits(0)
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import exact_events as ee

NV = 3


def clean(p):
    return {e: v for e, v in p.items() if v}


def const(c):
    return {(0,) * NV: F(c)} if c else {}


def var(i):
    e = [0] * NV
    e[i] = 1
    return {tuple(e): F(1)}


def add(*ps):
    out = {}
    for p in ps:
        for e, v in p.items():
            out[e] = out.get(e, 0) + v
    return clean(out)


def neg(p):
    return {e: -v for e, v in p.items()}


def sub(p, q):
    return add(p, neg(q))


def scale(p, c):
    return clean({e: v * c for e, v in p.items()})


def mul(p, q):
    out = {}
    for e, v in p.items():
        for f, w in q.items():
            g = tuple(x + y for x, y in zip(e, f))
            out[g] = out.get(g, 0) + v * w
    return clean(out)


def power(p, n):
    out = const(1)
    for _ in range(n):
        out = mul(out, p)
    return out


def binpoly(p, j):
    ans = const(1)
    for i in range(j):
        ans = mul(ans, sub(p, const(i)))
    return scale(ans, F(1, math.factorial(j)))


def roweval(row, p):
    return add(*(scale(binpoly(p, j), F(c)) for j, c in enumerate(row)))


def prefixpoly(row, p):
    return add(*(scale(binpoly(p, j + 1), F(c)) for j, c in enumerate(row)))


def gb(q, j):
    ans = F(1)
    for i in range(j):
        ans *= q - i
    return ans / math.factorial(j)


def evalrow(row, q, prefix=False):
    return sum(F(c) * gb(q, j + int(prefix)) for j, c in enumerate(row))


def count_matrix(maxlevel):
    """Derive counts from run lengths and nested sums, independent of supplied C."""
    models = {}
    models[2] = {"C": [[F(5), F(3)], [F(6), F(3)], [F(7), F(3)]], "actions": 4}
    for lev in range(3, maxlevel + 1):
        d = json.loads((ROOT / f"order{lev}_construction.json").read_text())
        prev = models[lev - 1]
        M = [[F(c) for c in row] for row in d["M"]]
        s = int(d["parent_stride"])
        assert all(c.denominator == 1 for row in M for c in row)

        def cv(q):
            L = s * (q + 1)
            ans = [
                evalrow(row, 2 * L, True) - evalrow(row, L, True) for row in prev["C"]
            ]
            return ans + [F(1)] + [evalrow(row, q) for row in M]

        vals = [cv(q) for q in range(lev)]
        C = []
        for i in range(len(vals[0])):
            dif = [v[i] for v in vals]
            coeff = []
            while dif:
                coeff.append(dif[0])
                dif = [dif[j + 1] - dif[j] for j in range(len(dif) - 1)]
            C.append(coeff)
        assert all(c.denominator == 1 for row in C for c in row)
        assert C == [[F(x) for x in row] for row in d["C"]]
        for q in [-3, lev, 17, 1001]:
            assert [evalrow(row, q) for row in C] == cv(q)
        models[lev] = {"C": C, "M": M, "s": s, "actions": len(C) + 1}
    return models


def compose_many(polys, subs):
    exps = {e for p in polys for e in p}
    powers = {}
    for i, p in enumerate(subs):
        maxpow = max((e[i] for e in exps), default=0)
        powers[i, 0] = const(1)
        for j in range(1, maxpow + 1):
            powers[i, j] = mul(powers[i, j - 1], p)
    images = {}
    for e in exps:
        z = const(1)
        for i, j in enumerate(e):
            z = mul(z, powers[i, j])
        images[e] = z
    return [add(*(scale(images[e], v) for e, v in p.items())) for p in polys]


def bernstein_coeff(p):
    degrees = [max((e[i] for e in p), default=0) for i in range(NV)]
    out = {}
    for idx in itertools.product(*(range(d + 1) for d in degrees)):
        val = F(0)
        for e, c in p.items():
            if all(a <= b for a, b in zip(e, idx)):
                fac = F(1)
                for a, b, d in zip(e, idx, degrees):
                    fac *= F(math.comb(b, a), math.comb(d, a))
                val += fac * c
        out[idx] = val
    return out, degrees


def bernstein_coeff_fast(p):
    degrees = [max((e[i] for e in p), default=0) for i in range(NV)]
    out = p.copy()
    for axis in reversed(range(NV)):
        transformed = {}
        d = degrees[axis]
        for e, v in out.items():
            a = e[axis]
            for i in range(a, d + 1):
                f = list(e)
                f[axis] = i
                f = tuple(f)
                transformed[f] = transformed.get(f, F(0)) + v * F(
                    math.comb(i, a), math.comb(d, a)
                )
        out = clean(transformed)
    return {
        i: out.get(i, F(0)) for i in itertools.product(*(range(d + 1) for d in degrees))
    }, degrees


def model(k, level=None, initial=None, Q=None):
    global NV
    level = level or k
    NV = level - 1
    data, D, B = ee.load(k)
    models = count_matrix(level)
    n = len(B)
    state0 = initial or [row[0] for row in B]
    Q = int(data["Q"]) if Q is None else Q
    certs = []
    bounds = [None] * NV

    def pushrun(state, a, length, tag):
        certs.append((tag + ".length_minus_one", sub(length, const(1)), False))
        last = [
            add(p, scale(sub(length, const(1)), B[j][a])) for j, p in enumerate(state)
        ]
        for endpoint, u in [("first", state), ("last", last)]:
            for j in range(n):
                if j != a:
                    certs.append((f"{tag}.{endpoint}.rival{j}", sub(u[a], u[j]), True))
        return [add(p, scale(length, B[j][a])) for j, p in enumerate(state)]

    def shiftcounts(state, counts):
        return [
            add(state[j], *(scale(c, B[j][i + 1]) for i, c in enumerate(counts)))
            for j in range(n)
        ]

    def phase(lev, q, state, nextvar):
        m = models[lev]
        if lev == 2:
            for a, row in zip((1, 2, 3), m["C"]):
                state = pushrun(state, a, roweval(row, q), f"L{lev}.a{a}")
            return state
        gw = models[lev - 1]["actions"]
        for a, row in enumerate(m["M"], gw + 1):
            state = pushrun(state, a, roweval(row, q), f"L{lev}.a{a}")
        L = scale(add(q, const(1)), m["s"])
        h = var(nextvar)
        bounds[nextvar] = sub(L, const(1))
        childq = add(L, h)
        certs.append((f"L{lev}.bundle_count_minus_one", sub(L, const(1)), False))
        pcounts = [
            sub(prefixpoly(row, childq), prefixpoly(row, L))
            for row in models[lev - 1]["C"]
        ]
        phase(lev - 1, childq, shiftcounts(state, pcounts), nextvar + 1)
        fullcounts = [
            sub(prefixpoly(row, scale(L, 2)), prefixpoly(row, L))
            for row in models[lev - 1]["C"]
        ]
        state = shiftcounts(state, fullcounts)
        return pushrun(state, gw, const(1), f"L{lev}.gateway{gw}")

    q = add(const(Q), var(0))
    counts = [
        sub(prefixpoly(row, q), prefixpoly(row, const(Q))) for row in models[level]["C"]
    ]
    start = shiftcounts([const(x) for x in state0], counts)
    end = phase(level, q, start, 1)
    return dict(
        k=k,
        level=level,
        Q=Q,
        data=data,
        D=D,
        B=B,
        state0=state0,
        models=models,
        certs=certs,
        bounds=bounds,
        phase_end=end,
    )


def certify(m, P, details=False):
    global NV
    assert isinstance(P, int) and P >= 1
    NV = m["level"] - 1
    start = time.monotonic()
    subs = [scale(var(0), P - 1)]
    for i in range(1, NV):
        # Future variables are untouched; this bound uses ancestors only.
        allsubs = subs + [var(j) for j in range(i, NV)]
        b = compose_many([m["bounds"][i]], allsubs)[0]
        subs.append(mul(b, var(i)))
    cert = m["certs"]
    normalized = compose_many([c[1] for c in cert], subs)
    failed = []
    coeffnum = 0
    mindigits = 0
    for (tag, p, strict), z in zip(cert, normalized):
        coeff, deg = bernstein_coeff_fast(z)
        coeffnum += len(coeff)
        mn = min(coeff.values())
        if mn < 0 or (strict and mn == 0):
            failed.append(
                {
                    "tag": tag,
                    "degrees": deg,
                    "min": str(mn),
                    "negative_coefficients": sum(v < 0 for v in coeff.values()),
                }
            )
            if len(failed) >= 10 and not details:
                break
    return {
        "status": "PASS" if not failed else "NOT_CERTIFIED",
        "k": m["k"],
        "level": m["level"],
        "Q": str(m["Q"]),
        "phases": str(P),
        "inequalities": len(cert),
        "bernstein_coefficients_tested": coeffnum,
        "seconds": time.monotonic() - start,
        "failed": failed,
    }, subs


def endpoint(m, P):
    Q = m["Q"]
    rows = m["models"][m["level"]]["C"]
    counts = [evalrow(row, Q + P, True) - evalrow(row, Q, True) for row in rows]
    assert all(c.denominator == 1 for c in counts)
    B = m["B"]
    state = [
        m["state0"][j] + sum(B[j][i + 1] * c for i, c in enumerate(counts))
        for j in range(len(B))
    ]
    return [int(c) for c in counts], [int(x) for x in state]


def main(argv=None):
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("--order", type=int, default=4)
    ap.add_argument("--phases", nargs="+", type=int, default=[1, 100, 100000000])
    a = ap.parse_args(argv)
    tick = time.monotonic()
    m = model(a.order)
    print(
        "MODEL",
        a.order,
        "seconds",
        time.monotonic() - tick,
        "inequalities",
        len(m["certs"]),
        flush=True,
    )
    results = []
    for P in a.phases:
        r, _ = certify(m, P)
        results.append(r)
        print(json.dumps(r), flush=True)
        if r["status"] == "PASS":
            c, s = endpoint(m, P)
            print(
                "ENDPOINT leader",
                ee.decision(s),
                "t digits",
                len(str(1 + sum(c))),
                flush=True,
            )
    (Path(__file__).parent / f"order{a.order}_initial_certificate.json").write_text(
        json.dumps(results, indent=2) + "\n"
    )
    if any(result["status"] != "PASS" for result in results):
        raise RuntimeError("NOT_CERTIFIED: the diagnostic result JSON was preserved")
    return results


if __name__ == "__main__":
    main()
