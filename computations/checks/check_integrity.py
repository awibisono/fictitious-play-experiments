"""Validate archived or freshly reproduced exact matrices and final states."""

from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import exact_events


def validate_coverage(certificates, initial_q, final_q):
    """Cover the full interval; archived prefix certificates may overlap."""
    assert certificates and 0 < initial_q < final_q
    intervals = []
    for certificate in certificates:
        assert certificate["status"] == "PASS"
        start = int(certificate["Q"])
        stop = start + int(certificate["phases"])
        assert initial_q <= start < stop <= final_q
        intervals.append((start, stop))
    covered_until = initial_q
    for start, stop in sorted(intervals):
        assert start <= covered_until, "Uncertified phase interval"
        covered_until = max(covered_until, stop)
    assert covered_until == final_q


def check():
    results = []
    for order in range(2, 7):
        construction, scale, matrix = exact_events.load(order)
        n = len(matrix)
        assert n == (order + 1) ** 2 - 5
        assert all(matrix[0][j] < 0 for j in range(1, n))
        path = (
            ROOT / f"order{order}_event_result.json"
            if order < 4
            else ROOT / "hierarchical" / f"order{order}_recursive_replay.json"
        )
        data = json.loads(path.read_text())
        assert data["order"] == order
        assert int(data["Q"]) == int(
            construction["Q"]
        ), "Result Q differs from construction"
        counts = list(map(int, data["counts"]))
        assert len(counts) == n and counts[0] == 1 and all(x >= 0 for x in counts)
        t = sum(counts)
        assert t == int(data["t"])
        assert scale == int(data["integer_scale"])
        assert data["matrix_sha256"] == construction["matrix_sha256"]
        scores = [sum(x * y for x, y in zip(row, counts)) for row in matrix]
        assert scores == list(map(int, data["final_scores_scaled"]))
        norm = max(abs(x) for row in matrix for x in row)
        assert norm == int(data["normalization_max_scaled"])
        assert (
            int(data["samples"][-1]["t"]) == t
        ), "Final sample time differs from counts"
        assert int(data["samples"][-1]["height_scaled"]) == max(
            scores
        ), "Final sample height differs from scores"
        assert Fraction(data["samples"][-1]["gap"]) == Fraction(
            2 * max(scores), scale * t
        )
        assert Fraction(data["samples"][-1]["normalized_gap"]) == Fraction(
            2 * max(scores), norm * t
        )
        if order >= 4:
            assert data["status"] == "PASS"
            assert all(
                x["k"] == order and x["level"] == order for x in data["certificates"]
            )
            assert int(data["final_q"]) == 4096 * int(data["Q"])
            assert int(data["completed_outer_phases"]) == int(data["final_q"]) - int(
                data["Q"]
            )
            validate_coverage(
                data["certificates"], int(data["Q"]), int(data["final_q"])
            )
        results.append(dict(order=order, actions=n, exact_state_checks="PASS"))
    summary = json.loads((ROOT / "summary.json").read_text())
    with localcontext() as context:
        context.prec = 100
        for record in summary:
            order = record["order"]
            construction, scale, matrix = exact_events.load(order)
            power = Fraction(construction["rate_constant_power_k"])
            norm = Fraction(max(abs(x) for row in matrix for x in row), scale)
            decimal = lambda x: Decimal(x.numerator) / Decimal(x.denominator)
            expected = decimal(power).log10() / order - decimal(norm).log10()
            assert abs(
                expected - Decimal(record["log10_normalized_constant"])
            ) < Decimal("1e-80")
    print(json.dumps(results, indent=2))
    return results


if __name__ == "__main__":
    check()
