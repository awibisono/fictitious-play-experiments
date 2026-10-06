#!/usr/bin/env python3
"""Run isolated, logged reproduction stages without changing bundled evidence."""

from pathlib import Path
import argparse
import importlib.metadata
import json
import os
import platform
import shutil
import subprocess
import sys
import time

from computations.reference_comparison import compare_reference

ROOT = Path(__file__).resolve().parent


def compare_outputs(fresh, original, mode):
    checks = []
    if mode == "construct":
        for order in range(2, 7):
            filename = f"order{order}_construction.json"
            old, new = [
                json.loads((root / filename).read_text()) for root in (original, fresh)
            ]
            old.pop("construction_seconds", None)
            new.pop("construction_seconds", None)
            assert old == new, filename
            checks.append(filename)
    if mode == "replay":
        for order in range(2, 7):
            filename = (
                f"order{order}_event_result.json"
                if order < 4
                else f"hierarchical/order{order}_recursive_replay.json"
            )
            old, new = [
                json.loads((root / filename).read_text()) for root in (original, fresh)
            ]
            if order < 4:
                old.pop("wall_seconds", None)
                new.pop("wall_seconds", None)
                compare_reference(new, old, filename)
            else:
                for key in (
                    "counts",
                    "final_scores_scaled",
                    "integer_scale",
                    "normalization_max_scaled",
                    "matrix_sha256",
                    "Q",
                    "final_q",
                    "completed_outer_phases",
                    "t",
                    "samples",
                ):
                    assert old[key] == new[key], (filename, key)
            checks.append(filename)
        filename = "hierarchical/order6_dense_certified_samples.json"
        old, new = [
            json.loads((root / filename).read_text()) for root in (original, fresh)
        ]
        assert old["samples"] == new["samples"], filename
        checks.append(filename)
    return checks


def prepare_plot_inputs(work, plot_work, reference_root):
    # Preserve raw replay outputs; use archived libm rounding only in plots.
    shutil.copytree(work, plot_work)
    for order in (2, 3):
        filename = f"order{order}_event_result.json"
        fresh = json.loads((plot_work / filename).read_text())
        reference = json.loads((reference_root / filename).read_text())
        compare_reference(fresh["samples"], reference["samples"], filename)
        for actual, expected in zip(fresh["samples"], reference["samples"]):
            for field in ("log10_t", "log10_gap", "log10_normalized_gap"):
                actual[field] = expected[field]
        (plot_work / filename).write_text(json.dumps(fresh, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "stage", choices=("smoke", "figures", "construct", "replay", "audit", "all")
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="A new directory; existing paths are refused",
    )
    args = parser.parse_args()
    if not __debug__:
        parser.error("Run without Python -O or -OO")
    output = args.output_dir.resolve()
    if output.exists():
        parser.error(f"Output already exists: {output}; choose a new directory")
    output.mkdir(parents=True)
    work = output / "computations"
    shutil.copytree(
        ROOT / "computations",
        work,
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "generated"),
    )
    env = os.environ.copy()
    env.update(
        PYTHONDONTWRITEBYTECODE="1",
        MPLCONFIGDIR=str(output / "matplotlib-cache"),
        SOURCE_DATE_EPOCH="1791062400",
    )
    begin = time.monotonic()
    report = dict(
        stage=args.stage,
        status="RUNNING",
        python=platform.python_version(),
        platform=platform.platform(),
        commands=[],
        comparisons=[],
    )
    report["dependencies"] = {}
    for name in ("sympy", "numpy", "matplotlib"):
        try:
            report["dependencies"][name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            report["dependencies"][name] = None

    def save():
        report["elapsed_seconds"] = time.monotonic() - begin
        (output / "run_report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(script, *arguments, cwd=None):
        command = [
            sys.executable,
            *([str(work / script)] if script else []),
            *map(str, arguments),
        ]
        label = Path(script).stem if script else "unit_tests"
        logfile = output / f"{len(report['commands']) + 1:02d}_{label}.log"
        print("RUN", " ".join(command), flush=True)
        start = time.monotonic()
        with logfile.open("w") as log:
            process = subprocess.run(
                command, cwd=cwd or work, env=env, stdout=log, stderr=subprocess.STDOUT
            )
        record = dict(
            command=command,
            exit_code=process.returncode,
            seconds=time.monotonic() - start,
            log=logfile.name,
        )
        report["commands"].append(record)
        save()
        if process.returncode:
            print(logfile.read_text()[-12000:], file=sys.stderr)
            raise RuntimeError(f"Failed {label}; see {logfile}")
        print("PASS", label, f"{record['seconds']:.2f}s", flush=True)

    try:
        if args.stage in ("smoke", "all"):
            run(
                None,
                "-m",
                "unittest",
                "discover",
                "-s",
                str(ROOT / "tests"),
                "-v",
                cwd=ROOT,
            )
            run("checks/check_integrity.py")
            run("checks/check_leading_coefficients.py")
        if args.stage in ("construct", "all"):
            run("construction.py", "--max-order", 6)
            run("build_constructions.py")
            report["comparisons"] += compare_outputs(
                work, ROOT / "computations", "construct"
            )
        if args.stage in ("replay", "all"):
            for order, events in ((2, 100000), (3, 1000000)):
                run(
                    "exact_events.py",
                    "--orders",
                    order,
                    "--events",
                    events,
                    "--seconds",
                    1e12,
                    "--publication-v5",
                )
            run(
                "hierarchical/run_recursive_replay.py",
                "--orders",
                4,
                5,
                "--doublings",
                12,
            )
            run("hierarchical/run_sextic_replay.py")
            run("hierarchical/extract_certified_sextic_samples.py")
            report["comparisons"] += compare_outputs(
                work, ROOT / "computations", "replay"
            )
            run("checks/check_integrity.py")
        if args.stage in ("audit", "all"):
            run("audit/independent_audit.py")
            run("checks/recheck_hierarchical_signs.py")
            run("hierarchical/audit/independent_sextic_full_signs.py")
            run("hierarchical/audit/audit_replay_outputs.py")
            run("hierarchical/audit/audit_sextic_dense.py")
        if args.stage in ("figures", "all"):
            if args.stage == "all":
                plot_work = output / "plot-inputs"
                prepare_plot_inputs(work, plot_work, ROOT / "computations")
                report["plot_log_rounding"] = (
                    "Archived descriptive logs used after absolute 1e-12 comparison; "
                    "raw replay outputs retained in computations."
                )
                work = plot_work
            run("plots/make_print_figures.py", "--output-dir", output / "figures")
        report["status"] = "PASS"
    except Exception as error:
        report["status"] = "FAIL"
        report["error"] = str(error)
        raise
    finally:
        save()
    print(
        "PASS",
        args.stage,
        f"{report['elapsed_seconds']:.2f}s; report: {output / 'run_report.json'}",
        flush=True,
    )


if __name__ == "__main__":
    main()
