"""Full independent sextic sign pass: no producer implementation imported.
Own monomial/Faulhaber word construction, cached monomial substitution, and
forward-axis grouped/pull tensor Bernstein conversion (producer uses reverse
axis coefficient pushes). All arithmetic exact rational.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, time, hashlib, random
from pathlib import Path
from fractions import Fraction as F
from math import comb
from itertools import product

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import independent_general_certificate as ind


def bernstein_pull(p):
    v = ind.V
    deg = tuple(max((e[i] for e in p), default=0) for i in range(v))
    a = dict(p)
    for axis, d in enumerate(deg):
        groups = {}
        for e, c in a.items():
            key = e[:axis] + e[axis + 1 :]
            groups.setdefault(key, {})[e[axis]] = c
        out = {}
        weights = {
            (i, j): F(comb(i, j), comb(d, j))
            for i in range(d + 1)
            for j in range(i + 1)
        }
        for key, co in groups.items():
            for i in range(d + 1):
                value = sum(c * weights[i, j] for j, c in co.items() if j <= i)
                if value:
                    out[key[:axis] + (i,) + key[axis:]] = value
        a = out
    return {e: a.get(e, F(0)) for e in product(*(range(d + 1) for d in deg))}, deg


def normalize_cached(model, lo, hi):
    x = ind.var(0)
    subs = [ind.add(ind.c(lo), ind.scale(x, hi - lo))]
    for i in range(1, ind.V):
        subs.append(
            ind.mul(
                ind.compose(
                    model["bounds"][i], subs + [ind.var(j) for j in range(i, ind.V)]
                ),
                ind.var(i),
            )
        )
    cache = {ind.Z: ind.c(1)}

    def image(e):
        if e not in cache:
            j = next(i for i in range(ind.V) if e[i])
            prev = list(e)
            prev[j] -= 1
            cache[e] = ind.mul(image(tuple(prev)), subs[j])
        return cache[e]

    for _, p, _ in model["cert"]:
        for e in p:
            image(e)

    def normalized(p):
        return ind.summ(ind.scale(cache[e], c) for e, c in p.items())

    return normalized, len(cache)


def selftest():
    rng = random.Random(820441)
    n = 0
    for v in range(1, 6):
        ind.V = v
        ind.Z = (0,) * v
        for _ in range(25):
            p = ind.clean(
                {
                    tuple(rng.randrange(4) for _ in range(v)): F(
                        rng.randrange(-17, 18), rng.randrange(1, 8)
                    )
                    for _ in range(rng.randrange(16))
                }
            )
            assert bernstein_pull(p) == ind.bernstein(p)
            n += 1
    return n


def run():
    begin = time.monotonic()
    tests = selftest()
    print("PULL_SELFTEST_PASS", tests, "seconds", time.monotonic() - begin, flush=True)
    model = ind.build(6)
    P = 4095 * model["Q"]
    print(
        "INDEPENDENT_MODEL_BUILT",
        "constraints",
        len(model["cert"]),
        "seconds",
        time.monotonic() - begin,
        flush=True,
    )
    norm, monomials = normalize_cached(model, 0, P - 1)
    print(
        "NORMALIZATION_READY",
        "monomials",
        monomials,
        "seconds",
        time.monotonic() - begin,
        flush=True,
    )
    tested = 0
    failed = []
    degrees = set()
    last = time.monotonic()
    for i, (tag, p, strict) in enumerate(model["cert"]):
        bp = norm(p)
        coeff, deg = bernstein_pull(bp)
        mn = min(coeff.values())
        tested += len(coeff)
        degrees.add(deg)
        if mn < 0 or (strict and mn == 0):
            failed.append(dict(tag=tag, minimum=str(mn), degree=deg))
        if i % 250 == 249 or i + 1 == len(model["cert"]):
            print(
                "PROGRESS",
                i + 1,
                "of",
                len(model["cert"]),
                "coefficients",
                tested,
                "failed",
                len(failed),
                "seconds",
                time.monotonic() - begin,
                flush=True,
            )
    out = dict(
        status="PASS" if not failed else "NOT_CERTIFIED",
        order=6,
        initial_q=str(model["Q"]),
        completed_phases=str(P),
        final_q=str(model["Q"] + P),
        inequalities=len(model["cert"]),
        bernstein_coefficients_tested=tested,
        failed=failed,
        degrees=sorted(degrees),
        independent_sign_recomputation=True,
        producer_code_imported=False,
        source_C_or_R_used=False,
        coefficient_conversion="Own forward-axis grouped pull transform, crosschecked against direct tensor formula",
        conversion_selftests=tests,
        seconds=time.monotonic() - begin,
        implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        independent_model_sha256=hashlib.sha256(
            Path(ind.__file__).read_bytes()
        ).hexdigest(),
    )
    (HERE / "independent_sextic_full_signs_results.json").write_text(
        json.dumps(out, indent=2) + "\n"
    )
    print("DONE", json.dumps(out), flush=True)
    if failed:
        raise RuntimeError(
            f"NOT_CERTIFIED: {len(failed)} sextic sign constraints failed; "
            "the diagnostic result JSON was preserved"
        )


if __name__ == "__main__":
    run()
