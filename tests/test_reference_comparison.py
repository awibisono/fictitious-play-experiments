"""Portable descriptive logs must never weaken exact scientific comparisons."""

import unittest

from computations.reference_comparison import compare_reference


class ReferenceComparisonTests(unittest.TestCase):
    def test_last_bit_log_rounding_is_accepted(self):
        compare_reference(
            {"log10_gap": -2.8075439094374137, "t": "123", "gap": "1/7"},
            {"log10_gap": -2.8075439094374133, "t": "123", "gap": "1/7"},
        )

    def test_exact_structural_and_large_log_changes_fail(self):
        expected = {"log10_gap": 1.0, "t": "123", "gap": "1/7", "events": 2}
        variants = [
            dict(expected, t="124"),
            dict(expected, gap="2/7"),
            dict(expected, events=2.0),
            dict(expected, log10_gap=1.000000001),
            dict(expected, log10_gap=float("nan")),
            dict(expected, extra=0),
        ]
        for actual in variants:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                compare_reference(actual, expected)
        with self.assertRaises(AssertionError):
            compare_reference([expected], [expected, expected])


class PlotInputTests(unittest.TestCase):
    def test_plot_rounding_preserves_raw_replay_and_rejects_exact_mismatch(self):
        import json
        import tempfile
        from pathlib import Path
        from reproduce import prepare_plot_inputs

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work, reference = root / "work", root / "reference"
            work.mkdir()
            reference.mkdir()
            actual = {
                "samples": [
                    {
                        "t": "123",
                        "gap": "1/7",
                        "log10_t": 1.0,
                        "log10_gap": -2.8075439094374137,
                        "log10_normalized_gap": -3.0,
                    }
                ]
            }
            expected = json.loads(json.dumps(actual))
            expected["samples"][0]["log10_gap"] = -2.8075439094374133
            for order in (2, 3):
                name = f"order{order}_event_result.json"
                (work / name).write_text(json.dumps(actual))
                (reference / name).write_text(json.dumps(expected))
            prepare_plot_inputs(work, root / "plots", reference)
            name = "order2_event_result.json"
            self.assertEqual(json.loads((work / name).read_text()), actual)
            self.assertEqual(json.loads((root / "plots" / name).read_text()), expected)
            actual["samples"][0]["t"] = "124"
            (work / name).write_text(json.dumps(actual))
            with self.assertRaises(AssertionError):
                prepare_plot_inputs(work, root / "bad-plots", reference)
