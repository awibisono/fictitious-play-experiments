"""Independent monomial/Faulhaber recursive finite-word verifier.
No source C/R phase tables are read. M and parent_stride propose a word only.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from fractions import Fraction as F
from math import comb, lcm
from itertools import product
from pathlib import Path
import sys, json, time, hashlib

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
V = 3
Z = (0,) * V


def clean(p):
    return {k: F(v) for k, v in p.items() if v}


def c(x):
    return {Z: F(x)} if x else {}


def var(i):
    return {tuple(int(j == i) for j in range(V)): F(1)}


def add(a, b):
    p = dict(a)
    for k, v in b.items():
        p[k] = p.get(k, 0) + v
    return clean(p)


def scale(p, x):
    return clean({k: v * x for k, v in p.items()})


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    p = {}
    for i, x in a.items():
        for j, y in b.items():
            k = tuple(i[t] + j[t] for t in range(V))
            p[k] = p.get(k, 0) + x * y
    return clean(p)


def power(p, n):
    v = c(1)
    for _ in range(n):
        v = mul(v, p)
    return v


def summ(ps):
    p = {}
    for v in ps:
        p = add(p, v)
    return p


def compose(p, subs):
    out = {}
    powers = {}
    for i, pol in enumerate(subs):
        powers[i, 0] = c(1)
        for j in range(1, max((e[i] for e in p), default=0) + 1):
            powers[i, j] = mul(powers[i, j - 1], pol)
    for exps, coeff in p.items():
        term = c(coeff)
        for i, e in enumerate(exps):
            term = mul(term, powers[i, e])
        out = add(out, term)
    return out


def at(p, vals):
    out = 0
    for exps, v in p.items():
        for e, x in zip(exps, vals):
            v *= x**e
        out += v
    return out


def bino(q, j):
    out = c(1)
    for i in range(j):
        out = scale(mul(out, sub(q, c(i))), F(1, i + 1))
    return out


def sum_powers(H, k):
    if k == 0:
        return H
    if k == 1:
        return scale(mul(H, sub(H, c(1))), F(1, 2))
    if k == 2:
        return scale(mul(mul(H, sub(H, c(1))), sub(scale(H, 2), c(1))), F(1, 6))
    if k == 3:
        return scale(mul(power(H, 2), power(sub(H, c(1)), 2)), F(1, 4))
    if k == 4:
        return scale(
            mul(
                mul(mul(H, sub(H, c(1))), sub(scale(H, 2), c(1))),
                sub(sub(scale(power(H, 2), 3), scale(H, 3)), c(1)),
            ),
            F(1, 30),
        )
    if k == 5:
        return scale(
            mul(
                mul(power(H, 2), power(sub(H, c(1)), 2)),
                sub(sub(scale(power(H, 2), 2), scale(H, 2)), c(1)),
            ),
            F(1, 12),
        )
    raise ValueError(k)


def sum_shifted(p, base, N):
    out = {}
    pow = {j: power(base, j) for j in range(max((e[0] for e in p), default=0) + 1)}
    sums = {j: sum_powers(N, j) for j in pow}
    for e, v in p.items():
        i = e[0]
        assert not any(e[1:])
        for r in range(i + 1):
            out = add(out, scale(mul(pow[i - r], sums[r]), v * comb(i, r)))
    return out


def build(order):
    global V, Z
    V = order - 1
    Z = (0,) * V
    ds = {
        k: json.loads((ROOT / f"order{k}_construction.json").read_text())
        for k in range(2, order + 1)
    }
    A = [[F(v) for v in r] for r in ds[order]["matrix"]]
    D = lcm(*(v.denominator for r in A for v in r))
    B = [[int(v * D) for v in r] for r in A]
    m = len(B)
    q = var(0)
    variables = [var(i) for i in range(V)]
    M = {
        k: [
            summ(scale(bino(q, j), F(x)) for j, x in enumerate(row))
            for row in ds[k]["M"]
        ]
        for k in range(3, order + 1)
    }
    C = {2: {a: add(scale(q, 3), c(a + 4)) for a in (1, 2, 3)}}
    gateway = {}
    stride = {}
    for lev in range(3, order + 1):
        gw = max(C[lev - 1]) + 1
        gateway[lev] = gw
        stride[lev] = int(ds[lev]["parent_stride"])
        L = scale(add(q, c(1)), stride[lev])
        C[lev] = {
            **{a: M[lev][a - gw - 1] for a in range(gw + 1, gw + 1 + len(M[lev]))},
            gw: c(1),
        }
        for a, p in C[lev - 1].items():
            C[lev][a] = sum_shifted(p, L, L)
    Q = int(ds[order]["Q"])
    topq = add(c(Q), q)
    topcounts = {a: compose(p, [topq] + variables[1:]) for a, p in C[order].items()}
    entry = [
        add(
            c(B[j][0]),
            summ(scale(sum_shifted(p, c(0), q), B[j][a]) for a, p in topcounts.items()),
        )
        for j in range(m)
    ]
    cert = []
    lengths = []
    bounds = [None] * V

    def margins(a, L, ss, tag):
        lengths.append((tag + ".length_minus_one", sub(L, c(1)), False))
        for last in (0, 1):
            off = sub(L, c(1)) if last else {}
            for j in range(m):
                if a != j:
                    cert.append(
                        (
                            tag + (".last" if last else ".first") + f".rival{j}",
                            add(sub(ss[a], ss[j]), scale(off, B[a][a] - B[j][a])),
                            True,
                        )
                    )

    def update(ss, a, L):
        return [add(x, scale(L, B[j][a])) for j, x in enumerate(ss)]

    def sumsupdate(ss, countpolys):
        return [
            add(x, summ(scale(p, B[j][a]) for a, p in countpolys.items()))
            for j, x in enumerate(ss)
        ]

    def phase(lev, qq, ss, idx):
        if lev == 2:
            for a in (1, 2, 3):
                L = compose(C[2][a], [qq] + variables[1:])
                margins(a, L, ss, f"L2.a{a}")
                ss = update(ss, a, L)
            return ss
        gw = gateway[lev]
        for a, p in zip(range(gw + 1, gw + 1 + len(M[lev])), M[lev]):
            L = compose(p, [qq] + variables[1:])
            margins(a, L, ss, f"L{lev}.a{a}")
            ss = update(ss, a, L)
        L = scale(add(qq, c(1)), stride[lev])
        offset = var(idx)
        bounds[idx] = sub(L, c(1))
        lengths.append((f"L{lev}.bundle_count_minus_one", sub(L, c(1)), False))
        prefix = {a: sum_shifted(p, L, offset) for a, p in C[lev - 1].items()}
        phase(lev - 1, add(L, offset), sumsupdate(ss, prefix), idx + 1)
        full = {a: sum_shifted(p, L, L) for a, p in C[lev - 1].items()}
        ss = sumsupdate(ss, full)
        margins(gw, c(1), ss, f"L{lev}.gateway{gw}")
        return update(ss, gw, c(1))

    phaseend = phase(order, topq, entry, 1)
    assert all(F(x).denominator == 1 for k in M for row in ds[k]["M"] for x in row)
    return dict(
        order=order,
        B=B,
        D=D,
        Q=Q,
        cert=cert + lengths,
        bounds=bounds,
        topcounts=topcounts,
        entry=entry,
        phaseend=phaseend,
        C=C,
    )


def flatten(model, P):
    subs = [scale(var(0), P - 1)]
    for idx in range(1, V):
        subs.append(
            mul(
                compose(model["bounds"][idx], subs + [var(j) for j in range(idx, V)]),
                var(idx),
            )
        )
    return subs


def bernstein(p):
    deg = tuple(max((k[i] for k in p), default=0) for i in range(V))
    out = {}
    for idx in product(*(range(d + 1) for d in deg)):
        val = F(0)
        for e, v in p.items():
            if any(e[i] > idx[i] for i in range(V)):
                continue
            for i in range(V):
                v *= F(comb(idx[i], e[i]), comb(deg[i], e[i]))
            val += v
        out[idx] = val
    return out, deg


def compare_model_to_candidate(ind, candidate):
    # Coefficient-by-coefficient agreement of every actual state/score margin,
    # counts from separate summation bases, and every domain polynomial.
    model = candidate.model(ind["order"])
    bytag = {tag: (p, strict) for tag, p, strict in model["certs"]}
    assert len(ind["cert"]) == len(model["certs"])
    for tag, p, strict in ind["cert"]:
        assert bytag[tag] == (p, strict), tag
    assert ind["bounds"] == model["bounds"]
    assert ind["phaseend"] == model["phase_end"]
    return model


def run(order, P):
    global V, Z
    tick = time.monotonic()
    model = build(order)
    print("BUILT", order, len(model["cert"]), time.monotonic() - tick, flush=True)
    sys.path.insert(0, str(HERE.parent))
    import certify_recursive_word as candidate

    cm = compare_model_to_candidate(model, candidate)
    print("ALL_POLYNOMIALS_MATCH", order, time.monotonic() - tick, flush=True)
    subs = flatten(model, P)
    fail = []
    coeffs = 0
    degset = set()
    for i, (tag, p, strict) in enumerate(model["cert"]):
        pp = compose(p, subs)
        bs, deg = bernstein(pp)
        coeffs += len(bs)
        mn = min(bs.values())
        degset.add(deg)
        assert (bs, list(deg)) == candidate.bernstein_coeff_fast(pp)
        if mn < 0 or (strict and mn == 0):
            fail.append(dict(tag=tag, minimum=str(mn)))
    out = dict(
        order=order,
        P=str(P),
        status="PASS" if not fail else "NOT_CERTIFIED",
        inequalities=len(model["cert"]),
        exact_coefficients_compared=coeffs,
        degrees=sorted(degset),
        failures=fail,
        seconds=time.monotonic() - tick,
        candidate_sha256=hashlib.sha256(
            Path(candidate.__file__).read_bytes()
        ).hexdigest(),
    )
    (HERE / f"independent_general_k{order}_results.json").write_text(
        json.dumps(out, indent=2) + "\n"
    )
    print(json.dumps(out), flush=True)
    return out


def main(argv=None):
    arguments = sys.argv[1:] if argv is None else argv
    order = int(arguments[0]) if arguments else 5
    P = (
        int(arguments[1])
        if len(arguments) > 1
        else 101
        * int(json.loads((ROOT / f"order{order}_construction.json").read_text())["Q"])
    )
    result = run(order, P)
    if result["status"] != "PASS":
        raise RuntimeError("NOT_CERTIFIED: the diagnostic result JSON was preserved")
    return result


if __name__ == "__main__":
    main()
