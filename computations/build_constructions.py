if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, time, hashlib
from pathlib import Path
from math import factorial

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
sys.path.insert(0, str(Path(__file__).parent))
import construction as v

root = Path(__file__).parent
mat = lambda A: [[str(x) for x in A.row(i)] for i in range(A.rows)]
cur = v.build_and_verify_rps_core()
for k in range(2, 7):
    start = time.monotonic()
    if k > 2:
        wit = v.lift_order(cur, verbose=True, plan_next=True)
        cert = v.verify_lift(wit)
        cur = wit["output_parent"]
    A, F, Fstar = v.install_strict_zero_start_game(cur, cur.threshold)
    cr = v.s.ones(1, cur.G.rows) * cur.C
    a = cr[k - 1] / factorial(k)
    b = cur.R[cur.b, k - 1] / factorial(k - 1)
    data = dict(
        order=k,
        Q=str(cur.threshold),
        matrix=mat(A),
        R=mat(cur.R),
        C=mat(cur.C),
        b=cur.b,
        tau=str(cur.tau),
        stride=str(cur.stride),
        a=str(a),
        b_star=str(b),
        rate_constant_power_k=str(2**k * b**k / a ** (k - 1)),
        setup_translation_bias=str(Fstar[cur.b] - F[cur.b]),
        construction_seconds=time.monotonic() - start,
    )
    if k > 2:
        data.update(
            M=mat(wit["M"]),
            parent_stride=str(wit["parent"].stride),
            scale_bits=wit["scale_bits"],
            radius_bits=wit["radius_bits"],
        )
    data["matrix_sha256"] = hashlib.sha256(
        json.dumps(data["matrix"], separators=(",", ":")).encode()
    ).hexdigest()
    (root / f"order{k}_construction.json").write_text(json.dumps(data, indent=2) + "\n")
    print(
        "BUILT",
        k,
        "Q digits",
        len(data["Q"]),
        "seconds",
        data["construction_seconds"],
        flush=True,
    )
