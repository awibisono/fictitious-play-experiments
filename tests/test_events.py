"""Independent exact tests for the installed low-order event engines.

Run from the release root: python -m unittest discover -s tests -v
No input is written. The exact engine rejects optimized Python.
"""

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout
import gzip
import io
import subprocess
import tempfile
from fractions import Fraction
from math import lcm

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
SOURCE = Path(__file__).resolve().parents[1] / "computations"


def import_engine(name):
    spec = importlib.util.spec_from_file_location(name, SOURCE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ENGINES = [import_engine("exact_events")]
ENGINE = ENGINES[0]


def qvalue(p, x):
    c, b, a = p
    return c + x * (b + a * x)


def oracle_first_nonpositive(p):
    """Discrete convexity and binary search; no roots or producer minima."""
    c, b, a = p
    if c <= 0:
        raise ValueError("positive initial value required")
    if a == 0 and b >= 0:
        return None
    if a > 0:
        # First location with nonnegative forward difference is a minimizer.
        high = max(0, -((b + a) // (2 * a)))
        if qvalue(p, high) > 0:
            return None
    else:
        high = 1
        while qvalue(p, high) > 0:
            high *= 2
    low = 0
    while high - low > 1:
        middle = (low + high) // 2
        if qvalue(p, middle) <= 0:
            high = middle
        else:
            low = middle
    return high


def unique_leader(s):
    candidates = [j for j in range(len(s)) if s[j] == max(s)]
    if len(candidates) != 1:
        raise ValueError("tie")
    return candidates[0]


def oracle_run(s, B):
    a = unique_leader(s)

    # Exponential and binary search on all simultaneous strict comparisons.
    def same(r):
        z = [v + r * B[j][a] for j, v in enumerate(s)]
        return all(z[a] > z[j] for j in range(len(z)) if j != a)

    high = 1
    while same(high):
        high *= 2
    low = 0
    while high - low > 1:
        middle = (high + low) // 2
        if same(middle):
            low = middle
        else:
            high = middle
    return a, high


def add_action(s, B, a, length):
    return [v + length * B[j][a] for j, v in enumerate(s)]


def independent_data(k):
    d = json.loads((SOURCE / f"order{k}_construction.json").read_text())
    A = [[Fraction(x) for x in row] for row in d["matrix"]]
    D = lcm(*(x.denominator for row in A for x in row))
    B = [[(x * D).numerator for x in row] for row in A]
    return d, A, D, B


class ExactHelpers(unittest.TestCase):
    def test_first_nonpositive_exhaustive_small(self):
        # Independent exhaustive finite oracle is complete here: a negative
        # leading term crosses by c+abs(b)+1; a convex minimum is before |b|+1.
        for c, b, a in itertools.product(range(1, 41), range(-40, 41), range(-8, 9)):
            p = (c, b, a)
            expected = next(
                (r for r in range(c + abs(b) + 2) if qvalue(p, r) <= 0), None
            )
            self.assertEqual(oracle_first_nonpositive(p), expected, p)
            for engine in ENGINES:
                self.assertEqual(
                    engine.first_nonpositive(p), expected, (engine.__name__, p)
                )

    def test_first_nonpositive_large_integer_cases(self):
        rng = random.Random(530)
        cases = []
        for digits in (10, 50, 200, 1000):
            h = 10**digits + 7
            # Exact double root, narrow interval with no integer hit, two roots,
            # concave polynomials, and linear roots on/around an integer.
            cases += [(h * h + e, -2 * h, 1) for e in (-1, 0, 1)]
            cases += [
                (4 * h * h + 4 * h + 1, -8 * h - 4, 4),
                (4 * h * h + 4 * h + 2, -8 * h - 4, 4),
                (1, h, -1),
                (h, 0, -1),
                (h, -3, 0),
            ]
        for _ in range(500):
            cases.append(
                (
                    rng.getrandbits(256) + 1,
                    rng.randrange(-(2**256), 2**256),
                    rng.randrange(-(2**128), 2**128),
                )
            )
        for p in cases:
            expected = oracle_first_nonpositive(p)
            for engine in ENGINES:
                self.assertEqual(engine.first_nonpositive(p), expected, p)

    def test_polymin_against_complete_scan(self):
        rng = random.Random(3217)
        for _ in range(12000):
            p = [rng.randrange(-1000000, 1000001) for _ in range(3)]
            u = rng.randrange(81)
            expected = min(qvalue(p, i) for i in range(u + 1))
            for engine in ENGINES:
                self.assertEqual(engine.polymin(p, u), expected, (p, u))
        for h in (10**100 + 3, 10**1000 + 1):
            for error in (-1, 0, 1):
                for engine in ENGINES:
                    self.assertEqual(
                        engine.polymin((h * h + error, -2 * h, 1), 2 * h), error
                    )

    def test_run_against_round_scan_on_random_states(self):
        rng = random.Random(479)
        tested = 0
        for _ in range(4000):
            n = rng.randrange(3, 9)
            B = [[0 for _ in range(n)] for _ in range(n)]
            for i in range(n):
                for j in range(i):
                    B[i][j] = rng.randrange(-9, 10)
                    B[j][i] = -B[i][j]
            a = rng.randrange(1, n)
            s = [rng.randrange(-50, 0) for _ in range(n)]
            s[a] = rng.randrange(1, 51)
            if not any(B[j][a] > 0 for j in range(n)):
                continue
            expected = next(
                r
                for r in range(1, 102)
                if not all(s[a] > s[j] + r * B[j][a] for j in range(n) if j != a)
            )
            for engine in ENGINES:
                self.assertEqual(engine.run(s, B), (a, expected))
            tested += 1
        self.assertGreater(tested, 3000)


class InstalledData(unittest.TestCase):
    def test_construction_and_saved_state_invariants(self):
        for k in (2, 3):
            d, A, D, B = independent_data(k)
            n = (k + 1) ** 2 - 5
            self.assertEqual(len(A), n)
            self.assertTrue(all(len(row) == n for row in A))
            self.assertTrue(
                all(A[i][j] == -A[j][i] for i in range(n) for j in range(n))
            )
            self.assertEqual(
                d["matrix_sha256"],
                hashlib.sha256(
                    json.dumps(d["matrix"], separators=(",", ":")).encode()
                ).hexdigest(),
            )
            saved = json.loads((SOURCE / f"order{k}_event_result.json").read_text())
            counts = list(map(int, saved["counts"]))
            state = [sum(B[i][j] * counts[j] for j in range(n)) for i in range(n)]
            self.assertEqual(counts[0], 1)
            self.assertTrue(all(c >= 0 for c in counts))
            self.assertEqual(sum(counts), int(saved["t"]))
            self.assertEqual(state, list(map(int, saved["final_scores_scaled"])))
            self.assertEqual(int(saved["integer_scale"]), D)
            self.assertEqual(saved["matrix_sha256"], d["matrix_sha256"])
            norm = max(abs(x) for row in B for x in row)
            for p in saved["samples"]:
                t, h = int(p["t"]), int(p["height_scaled"])
                self.assertEqual(Fraction(p["gap"]), Fraction(2 * h, D * t))
                self.assertEqual(
                    Fraction(p["normalized_gap"]), Fraction(2 * h, norm * t)
                )
            # Compute both row maximization and column minimization payoffs.
            t = sum(counts)
            row = [
                sum(A[i][j] * Fraction(counts[j], t) for j in range(n))
                for i in range(n)
            ]
            col = [
                sum(A[i][j] * Fraction(counts[i], t) for i in range(n))
                for j in range(n)
            ]
            self.assertEqual(max(row) - min(col), Fraction(saved["samples"][-1]["gap"]))

    def test_direct_simultaneous_prefix_and_jump(self):
        for k in (2, 3):
            _, _, _, B = independent_data(k)
            s = [row[0] for row in B]
            z = s[:]
            counts = [0] * len(B)
            for _ in range(5000):
                row_action = unique_leader(z)
                # Column scores from skew symmetry; independent minimization.
                col = [-v for v in z]
                column_action = min(range(len(col)), key=col.__getitem__)
                self.assertEqual(row_action, column_action)
                z = add_action(z, B, column_action, 1)
                counts[row_action] += 1
            for engine in ENGINES:
                self.assertEqual(engine.stepwise(s, B, 5000), (z, counts))
                self.assertEqual(engine.jump_to(s, B, 5000), (z, counts))

    def test_batches_against_independent_event_replay(self):
        # Small caps let us independently replay EVERY constituent run, not
        # merely compare two implementations of the quadratic endpoint formula.
        for k in (2, 3):
            _, _, _, B = independent_data(k)
            s = [row[0] for row in B]
            batches = 0
            rejected_caps = 0
            actions_seen = set()
            for event in range(600):
                cap = (1, 2, 3, 7, 13, 41)[event % 6]
                baseline = ENGINES[0].cycle_batch(s, B, cap)
                for engine in ENGINES[1:]:
                    self.assertEqual(engine.cycle_batch(s, B, cap), baseline)
                self.assertEqual(ENGINES[0].run(s, B), oracle_run(s, B))
                if baseline is None:
                    a, ell = oracle_run(s, B)
                    actions_seen.add(a)
                    s = add_action(s, B, a, ell)
                    continue
                N, delta, expected_counts, checks, lengths = baseline
                actions_seen.update((1, 2, 3))
                self.assertGreaterEqual(N, 1)
                self.assertLessEqual(N, cap)
                self.assertEqual(checks, 6 * (len(B) - 1))
                z = s[:]
                counts = {1: 0, 2: 0, 3: 0}
                for r in range(N):
                    for a in (1, 2, 3):
                        actual_a, actual_length = oracle_run(z, B)
                        self.assertEqual(actual_a, a)
                        self.assertEqual(actual_length, lengths[a - 1] + 3 * r)
                        counts[a] += actual_length
                        # Check exact pre-round choices on both run endpoints.
                        self.assertEqual(unique_leader(z), a)
                        self.assertEqual(
                            unique_leader(add_action(z, B, a, actual_length - 1)), a
                        )
                        z = add_action(z, B, a, actual_length)
                self.assertEqual(z, [x + y for x, y in zip(s, delta)])
                self.assertEqual(counts, expected_counts)
                # If the cap did not bind, extending the proposed word must fail.
                if N < cap:
                    failed = False
                    zz = z[:]
                    for a in (1, 2, 3):
                        proposed = lengths[a - 1] + 3 * N
                        if (
                            unique_leader(zz) != a
                            or unique_leader(add_action(zz, B, a, proposed - 1)) != a
                        ):
                            failed = True
                        zz = add_action(zz, B, a, proposed)
                    self.assertTrue(failed)
                    rejected_caps += 1
                s = z
                batches += 1
            self.assertGreater(batches, 5)
            self.assertEqual(actions_seen, set(range(1, len(B))))
            if k == 3:
                self.assertGreater(rejected_caps, 0)


class InputGuards(unittest.TestCase):
    def setUp(self):
        _, _, _, self.B = independent_data(2)
        self.s = [row[0] for row in self.B]

    def test_decision_rejects_ties_setup_and_inexact_scores(self):
        for s in ([], [1, 1], [2, 1], [0, 1.0], [False, True]):
            with self.subTest(s=s), self.assertRaises(ValueError):
                ENGINE.decision(s)

    def test_round_counts_are_nonnegative_integers(self):
        for method in (ENGINE.stepwise, ENGINE.jump_to):
            for count in (-1, -100, 1.5, True):
                with (
                    self.subTest(method=method.__name__, count=count),
                    self.assertRaises(ValueError),
                ):
                    method(self.s, self.B, count)
            self.assertEqual(method(self.s, self.B, 0), (self.s, [0] * len(self.s)))

    def test_cycle_cap_must_be_positive_integer(self):
        # Original code produced negative counts on this later valid state.
        s = self.s[:]
        for _ in range(30):
            a, length = oracle_run(s, self.B)
            s = add_action(s, self.B, a, length)
        for cap in (-1, -100, 0, 1.5, True):
            with self.subTest(cap=cap), self.assertRaises(ValueError):
                ENGINE.cycle_batch(s, self.B, cap)

    def test_quadratic_domains_and_exact_types(self):
        for p in ((1, 2), (1, 2, 3, 4), (1.0, -1, 0), (True, -1, 0)):
            for call in (
                lambda: ENGINE.first_nonpositive(p),
                lambda: ENGINE.polymin(p, 10),
            ):
                with self.subTest(p=p), self.assertRaises(ValueError):
                    call()
        for c in (-1, 0):
            with self.assertRaises(ValueError):
                ENGINE.first_nonpositive((c, 1, 1))
        for u in (-1, 0.5, True):
            with self.subTest(u=u), self.assertRaises(ValueError):
                ENGINE.polymin((1, -1, 0), u)

    def test_run_rejects_bad_shape_diagonal_and_infinite_plateau(self):
        bad_matrices = ([[0]], [[0, 0], [0, 1]], [[0, 0], [0, 0]], [[0, 1.5], [-1, 0]])
        for matrix in bad_matrices:
            with self.subTest(matrix=matrix), self.assertRaises(ValueError):
                ENGINE.run([0, 1], matrix)

    def test_logarithm_requires_positive_integer(self):
        for n in (-1, 0, 1.0, True):
            with self.subTest(n=n), self.assertRaises(ValueError):
                ENGINE.logint(n)

    def test_execute_rejects_invalid_limits_before_loading_or_writing(self):
        calls = [
            (0, 1, 1),
            (-1, 1, 1),
            (True, 1, 1),
            (1.5, 1, 1),
            (1, 0, 1),
            (1, -1, 1),
            (1, float("nan"), 1),
            (1, float("inf"), 1),
            (1, 1, 0),
            (1, 1, -1),
            (1, 1, float("nan")),
            (1, 1, float("inf")),
        ]
        with patch.object(ENGINE, "load") as loader:
            for args in calls:
                with self.subTest(args=args), self.assertRaises(ValueError):
                    ENGINE.execute(2, *args)
            loader.assert_not_called()

    def test_installed_order_range(self):
        for k in (1, 7, 2.0, True):
            with self.subTest(k=k), self.assertRaises(ValueError):
                ENGINE.load(k)

    def test_construction_rejects_forged_hash_and_changed_matrix(self):
        original = json.loads((SOURCE / "order2_construction.json").read_text())
        variants = []
        fake = json.loads(json.dumps(original))
        fake["matrix_sha256"] = "0" * 64
        variants.append(fake)
        changed = json.loads(json.dumps(original))
        changed["matrix"][0][1] = "-1"
        variants.append(changed)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for d in variants:
                (root / "order2_construction.json").write_text(json.dumps(d))
                with (
                    patch.object(ENGINE, "ROOT", root),
                    self.assertRaisesRegex(ValueError, "SHA256"),
                ):
                    ENGINE.load(2)

    def test_construction_rejects_incorrect_shape_order_and_skew_symmetry(self):
        original = json.loads((SOURCE / "order2_construction.json").read_text())
        variants = []
        wrong_order = json.loads(json.dumps(original))
        wrong_order["order"] = 3
        variants.append(wrong_order)
        wrong_shape = json.loads(json.dumps(original))
        wrong_shape["matrix"].pop()
        variants.append(wrong_shape)
        wrong_skew = json.loads(json.dumps(original))
        wrong_skew["matrix"][0][1] = "-1"
        variants.append(wrong_skew)
        inexact = json.loads(json.dumps(original))
        inexact["matrix"][0][1] = -1.0
        variants.append(inexact)
        wrong_q = json.loads(json.dumps(original))
        wrong_q["Q"] = "1/2"
        variants.append(wrong_q)
        for d in variants:
            d["matrix_sha256"] = hashlib.sha256(
                json.dumps(d["matrix"], separators=(",", ":")).encode()
            ).hexdigest()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for d in variants:
                (root / "order2_construction.json").write_text(json.dumps(d))
                with patch.object(ENGINE, "ROOT", root), self.assertRaises(ValueError):
                    ENGINE.load(2)

    def test_optimized_python_is_rejected_at_import(self):
        command = [
            sys.executable,
            "-O",
            "-c",
            "import sys; sys.path.insert(0, sys.argv[1]); import exact_events",
            str(SOURCE),
        ]
        result = subprocess.run(command, capture_output=True, text=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires Python without -O or -OO", result.stderr)


class PublicationReplay(unittest.TestCase):
    def test_publication_cap_sampling_and_transcript(self):
        # Crosses the archival cap activation near sampled event 1331.
        saved = json.loads((SOURCE / "order2_event_result.json").read_text())
        expected = [p for p in saved["samples"] if p["event"] <= 1500]
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "order2_construction.json").write_bytes(
                (SOURCE / "order2_construction.json").read_bytes()
            )
            with patch.object(ENGINE, "ROOT", root), redirect_stdout(io.StringIO()):
                result = ENGINE.execute(2, 1500, 1e9, 1000, publication_v5=True)
            from computations.reference_comparison import compare_reference

            compare_reference(result["samples"][:-1], expected)
            self.assertEqual(result["events"], 1500)
            self.assertEqual(sum(map(int, result["counts"])), int(result["t"]))
            with gzip.open(root / "order2_event_transcript.jsonl.gz", "rt") as stream:
                records = [json.loads(line) for line in stream]
            self.assertEqual(len(records), 1500)
            self.assertEqual(records[-1]["t"], result["t"])
            self.assertEqual(max(int(p["cycles"]) for p in records), 2**40)
            self.assertEqual(
                json.loads((root / "order2_event_result.json").read_text()), result
            )


if __name__ == "__main__":
    unittest.main(verbosity=2)
