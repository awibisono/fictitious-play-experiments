"""Independent exact leading-coefficient audit; no constructor functions imported."""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
out = []
prev = None
for k in range(2, 7):
    d = json.loads((root / f"order{k}_construction.json").read_text())
    C = [[F(x) for x in r] for r in d["C"]]
    R = [[F(x) for x in r] for r in d["R"]]
    m = len(C)
    L = sum(r[-1] for r in C)
    xi = R[d["b"]][-1]
    a = L / factorial(k)
    h = xi / factorial(k - 1)
    assert a == F(d["a"])
    assert h == F(d["b_star"])
    assert 2**k * h**k / a ** (k - 1) == F(d["rate_constant_power_k"])
    assert m + 1 == (k + 1) ** 2 - 5
    row = {
        "order": k,
        "recurrent_actions": m,
        "installed_actions": m + 1,
        "count_top_positive": L > 0,
        "height_top_positive": xi > 0,
        "constant_verified": True,
    }
    if prev:
        dimprev, stride, prevL, prevxi = prev
        assert xi == prevxi * stride ** (k - 2) * (2 ** (k - 2) - 1)
        parent_contribution = prevL * stride ** (k - 1) * (2 ** (k - 1) - 1)
        reset_contribution = sum(r[-1] for r in C[dimprev + 1 :])
        assert L == parent_contribution + reset_contribution
        assert reset_contribution > 0
        row["lift_top_coefficients_verified"] = True
    out.append(row)
    prev = (m, F(d["stride"]), L, xi)
Path(__file__).with_name("leading_coefficient_check.json").write_text(
    json.dumps(out, indent=2) + "\n"
)
print(json.dumps(out, indent=2))
