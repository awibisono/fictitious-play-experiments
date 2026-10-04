"""Certify the entire sextic interval from its initial state, then extract samples."""

from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import time

import certify_recursive_word as certificate

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")


def execute():
    start = time.monotonic()
    model = certificate.model(6)
    q0, scale, matrix = model["Q"], model["D"], model["B"]
    phases = 4095 * q0
    result, _ = certificate.certify(model, phases)
    if result["status"] != "PASS":
        raise AssertionError(result)
    norm = max(abs(x) for row in matrix for x in row)
    constant_power = Fraction(model["data"]["rate_constant_power_k"])
    samples = []
    for q in (q0, q0 + 1, 101 * q0, 4096 * q0):
        increments, state = certificate.endpoint(model, q - q0)
        counts = [1] + increments
        t = sum(counts)
        height = max(state)
        gap = Fraction(2 * height, scale * t)
        assert state == [sum(x * y for x, y in zip(row, counts)) for row in matrix]
        with localcontext() as context:
            context.prec = 90

            def decimal(value):
                return Decimal(value.numerator) / Decimal(value.denominator)

            record = dict(
                q=str(q),
                t=str(t),
                gap=str(gap),
                normalized_gap=str(Fraction(2 * height, norm * t)),
                height_scaled=str(height),
                log10_t=str(Decimal(t).log10()),
                log10_normalized_gap=str(
                    decimal(Fraction(2 * height, norm * t)).log10()
                ),
                ratio_to_asymptote=str(
                    decimal(gap)
                    * Decimal(t) ** (Decimal(1) / 6)
                    / decimal(constant_power) ** (Decimal(1) / 6)
                ),
            )
            if samples:
                previous = samples[-1]
                record["previous_secant"] = str(
                    decimal(gap / Fraction(previous["gap"])).ln()
                    / (Decimal(t) / Decimal(previous["t"])).ln()
                )
        samples.append(record)
    output = dict(
        status="PASS",
        method="Fresh full-horizon exact finite-word certificate; no cached certificate is trusted",
        order=6,
        actions=len(matrix),
        Q=str(q0),
        final_q=str(4096 * q0),
        completed_outer_phases=str(phases),
        t=str(t),
        counts=list(map(str, counts)),
        final_scores_scaled=list(map(str, state)),
        integer_scale=str(scale),
        normalization_max_scaled=str(norm),
        matrix_sha256=model["data"]["matrix_sha256"],
        engine_sha256=hashlib.sha256(
            Path(certificate.__file__).read_bytes()
        ).hexdigest(),
        certificates=[result],
        samples=samples,
        elapsed_seconds=time.monotonic() - start,
    )
    path = Path(__file__).parent / "order6_recursive_replay.json"
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(
        "PASS sextic full horizon",
        result["inequalities"],
        "inequalities;",
        result["bernstein_coefficients_tested"],
        "coefficients",
        flush=True,
    )
    return output


if __name__ == "__main__":
    execute()
