"""Compare exact replay data with portable tolerances for descriptive logarithms."""

import math

LOG_FIELDS = frozenset(("log10_t", "log10_gap", "log10_normalized_gap"))


def compare_reference(actual, expected, path="result"):
    """Require exact data equality except for platform-dependent libm rounding."""
    if isinstance(expected, dict):
        assert isinstance(actual, dict) and actual.keys() == expected.keys(), path
        for key, value in expected.items():
            if key in LOG_FIELDS and isinstance(value, float):
                assert isinstance(actual[key], float) and math.isclose(
                    actual[key], value, rel_tol=0, abs_tol=1e-12
                ), f"{path}.{key}"
            else:
                compare_reference(actual[key], value, f"{path}.{key}")
    elif isinstance(expected, list):
        assert isinstance(actual, list) and len(actual) == len(expected), path
        for index, (a, e) in enumerate(zip(actual, expected)):
            compare_reference(a, e, f"{path}[{index}]")
    else:
        assert type(actual) is type(expected) and actual == expected, path
