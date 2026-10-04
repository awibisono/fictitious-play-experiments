"""Independent algebra, domain, and certificate regressions."""

from fractions import Fraction
from pathlib import Path
import itertools
import json
import random
import subprocess
import sys
import unittest
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [
    str(ROOT / "computations"),
    str(ROOT / "computations/hierarchical"),
    str(ROOT / "computations/hierarchical/audit"),
]
import certify_recursive_word as candidate
import independent_general_certificate as oracle

sys.path.insert(0, str(ROOT / "computations/checks"))
from check_integrity import validate_coverage
import check_integrity


def evaluate(polynomial, values):
    return sum(
        coefficient * product(value**degree for value, degree in zip(values, exponent))
        for exponent, coefficient in polynomial.items()
    )


def product(values):
    result = 1
    for value in values:
        result *= value
    return result


class CertificateTests(unittest.TestCase):
    def test_certificate_interval_union(self):
        with self.assertRaises(AssertionError):
            validate_coverage([], 0, 0)
        with self.assertRaises(AssertionError):
            validate_coverage([], 10, 11)
        certificates = [
            dict(status="PASS", Q="10", phases="1"),
            dict(status="PASS", Q="10", phases="1000"),
            dict(status="PASS", Q="1010", phases="90"),
        ]
        validate_coverage(certificates, 10, 1100)
        certificates[-1]["Q"] = "1011"
        certificates[-1]["phases"] = "89"
        with self.assertRaisesRegex(AssertionError, "Uncertified"):
            validate_coverage(certificates, 10, 1100)

    def test_saved_result_q_is_bound_to_construction(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            construction = ROOT / "computations/order2_construction.json"
            (root / construction.name).write_bytes(construction.read_bytes())
            (root / "order2_event_result.json").write_text(
                json.dumps({"order": 2, "Q": "0"})
            )
            with (
                patch.object(check_integrity, "ROOT", root),
                patch.object(check_integrity.exact_events, "ROOT", root),
            ):
                with self.assertRaisesRegex(AssertionError, "Result Q"):
                    check_integrity.check()

    def test_final_sample_metadata_is_bound_to_actual_state(self):
        for field in ("t", "height_scaled"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                construction = ROOT / "computations/order2_construction.json"
                (root / construction.name).write_bytes(construction.read_bytes())
                result = json.loads(
                    (ROOT / "computations/order2_event_result.json").read_text()
                )
                result["samples"][-1][field] = "0"
                (root / "order2_event_result.json").write_text(json.dumps(result))
                with (
                    patch.object(check_integrity, "ROOT", root),
                    patch.object(check_integrity.exact_events, "ROOT", root),
                ):
                    with self.assertRaisesRegex(AssertionError, "Final sample"):
                        check_integrity.check()

    def test_tensor_bernstein_against_direct_basis(self):
        randomizer = random.Random(83442)
        for dimensions in range(1, 5):
            candidate.NV = oracle.V = dimensions
            oracle.Z = (0,) * dimensions
            for _ in range(10):
                p = {
                    tuple(randomizer.randrange(3) for _ in range(dimensions)): Fraction(
                        randomizer.randrange(-10, 11), randomizer.randrange(1, 8)
                    )
                    for _ in range(9)
                }
                expected, degrees = oracle.bernstein(p)
                actual, actual_degrees = candidate.bernstein_coeff_fast(p)
                self.assertEqual(expected, actual)
                self.assertEqual(list(degrees), actual_degrees)
                point = [
                    Fraction(randomizer.randrange(11), 10) for _ in range(dimensions)
                ]
                self.assertGreaterEqual(evaluate(p, point), min(actual.values()))
                self.assertLessEqual(evaluate(p, point), max(actual.values()))

    def test_count_sums_and_all_margin_polynomials_independent(self):
        for order in (2, 3, 4):
            independent = oracle.build(order)
            model = oracle.compare_model_to_candidate(independent, candidate)
            self.assertEqual(len(independent["cert"]), len(model["certs"]))
            for phases in (0, 1, 3):
                counts, scores = candidate.endpoint(model, phases)
                point = (phases,) + (0,) * (order - 2)
                independent_scores = [
                    int(oracle.at(p, point)) for p in independent["entry"]
                ]
                self.assertEqual(scores, independent_scores)
                self.assertTrue(all(x >= 0 for x in counts))

    def test_faulhaber_formulas_against_integer_sums(self):
        oracle.V = 1
        oracle.Z = (0,)
        for power, horizon in itertools.product(range(6), range(16)):
            p = oracle.sum_powers(oracle.var(0), power)
            self.assertEqual(
                oracle.at(p, (horizon,)), sum(i**power for i in range(horizon))
            )

    def test_not_certified_is_not_a_counterexample(self):
        candidate.NV = 1
        p = {(0,): Fraction(26, 100), (1,): Fraction(-1), (2,): Fraction(1)}
        model = dict(
            level=2, k=2, Q=0, bounds=[None], certs=[("positive_quadratic", p, True)]
        )
        result, _ = candidate.certify(model, 2)
        self.assertEqual("NOT_CERTIFIED", result["status"])
        self.assertTrue(all(evaluate(p, [Fraction(i, 100)]) > 0 for i in range(101)))

    def test_strict_and_nonstrict_zero(self):
        for strict, status in ((True, "NOT_CERTIFIED"), (False, "PASS")):
            model = dict(level=2, k=2, Q=0, bounds=[None], certs=[("zero", {}, strict)])
            result, _ = candidate.certify(model, 1)
            self.assertEqual(status, result["status"])

    def test_constructor_metadata_and_count_tables(self):
        models = candidate.count_matrix(6)
        for order in range(2, 7):
            data = json.loads(
                (ROOT / "computations" / f"order{order}_construction.json").read_text()
            )
            self.assertEqual(len(data["matrix"]), (order + 1) ** 2 - 5)
            self.assertEqual(
                models[order]["C"], [[Fraction(x) for x in row] for row in data["C"]]
            )

    def test_optimized_python_is_rejected(self):
        for file in (
            "exact_events.py",
            "construction.py",
            "hierarchical/certify_recursive_word.py",
            "hierarchical/audit/independent_general_certificate.py",
            "checks/check_integrity.py",
        ):
            completed = subprocess.run(
                [sys.executable, "-O", str(ROOT / "computations" / file)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(0, completed.returncode, file)
            self.assertIn("without", completed.stderr)


if __name__ == "__main__":
    unittest.main()
