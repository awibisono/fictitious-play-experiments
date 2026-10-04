"""A failed independent sign check must not look like a successful command."""

from contextlib import redirect_stdout
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import io
import json
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "computations/hierarchical/audit"))
import independent_sextic_full_signs as sextic
import independent_general_certificate as independent

sys.path.insert(0, str(ROOT / "computations/hierarchical"))
import certify_recursive_word as candidate


class AuditFailureTests(unittest.TestCase):
    def test_failed_sextic_sign_check_preserves_diagnostics_then_raises(self):
        # Replace only expensive mathematical work. Exercise the real reporting,
        # file-writing, and error propagation path with one strict bad margin.
        fake = {"Q": 1, "cert": [("injected_bad_margin", {(0,): Fraction(-1)}, True)]}
        with TemporaryDirectory() as temp:
            output = Path(temp)
            with (
                patch.object(sextic, "HERE", output),
                patch.object(sextic, "selftest", return_value=0),
                patch.object(sextic.ind, "build", return_value=fake),
                patch.object(sextic, "normalize_cached", return_value=(lambda p: p, 1)),
                patch.object(
                    sextic,
                    "bernstein_pull",
                    return_value=({(0,): Fraction(-1)}, (0,)),
                ),
                redirect_stdout(io.StringIO()),
                self.assertRaisesRegex(RuntimeError, "NOT_CERTIFIED"),
            ):
                sextic.run()
            report = json.loads(
                (output / "independent_sextic_full_signs_results.json").read_text()
            )
            self.assertEqual(report["status"], "NOT_CERTIFIED")
            self.assertEqual(report["inequalities"], 1)
            self.assertEqual(report["bernstein_coefficients_tested"], 1)
            self.assertEqual(
                report["failed"],
                [{"tag": "injected_bad_margin", "minimum": "-1", "degree": [0]}],
            )

    def test_general_certificate_cli_rejects_failed_status(self):
        failed = {"status": "NOT_CERTIFIED", "failures": [{"minimum": "-1"}]}
        with patch.object(independent, "run", return_value=failed) as run:
            with self.assertRaisesRegex(RuntimeError, "NOT_CERTIFIED"):
                independent.main(["2", "1"])
            run.assert_called_once_with(2, 1)
        # A successful structured result is unchanged by CLI status handling.
        passed = {"status": "PASS", "failures": []}
        with patch.object(independent, "run", return_value=passed):
            self.assertIs(independent.main(["2", "1"]), passed)

    def test_producer_cli_preserves_failed_json_without_calculating_endpoint(self):
        failed = {"status": "NOT_CERTIFIED", "failed": [{"min": "-1"}]}
        model = {"certs": ["injected_margin"]}
        with TemporaryDirectory() as temp:
            output = Path(temp)
            with (
                patch.object(
                    candidate, "__file__", str(output / "certify_recursive_word.py")
                ),
                patch.object(candidate, "model", return_value=model),
                patch.object(candidate, "certify", return_value=(failed, [])),
                patch.object(candidate, "endpoint") as endpoint,
                redirect_stdout(io.StringIO()),
                self.assertRaisesRegex(RuntimeError, "NOT_CERTIFIED"),
            ):
                candidate.main(["--order", "2", "--phases", "1"])
            endpoint.assert_not_called()
            saved = json.loads((output / "order2_initial_certificate.json").read_text())
            self.assertEqual(saved, [failed])

    def test_callable_certificate_retains_structured_failure(self):
        model = {
            "level": 2,
            "k": 2,
            "Q": 0,
            "bounds": [None],
            "certs": [("strict_zero", {}, True)],
        }
        result, _ = candidate.certify(model, 1)
        self.assertEqual(result["status"], "NOT_CERTIFIED")
        self.assertEqual(result["failed"][0]["min"], "0")


if __name__ == "__main__":
    unittest.main()
