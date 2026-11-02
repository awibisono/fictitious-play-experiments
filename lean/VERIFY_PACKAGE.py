#!/usr/bin/env python3
"""Fail-closed integrity checks for the public Lean source export.

This verifies a supplied manifest; it is not a signature or a mathematical audit.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
PIN = "23f53ae238d01b1be52c981434c6abaef5cd49c9"
GENERATED = {".lake", "reproduction-output"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(relative):
    path = PurePosixPath(relative)
    require(bool(relative) and not path.is_absolute(), f"Invalid path: {relative!r}")
    require(".." not in path.parts and "." not in path.parts,
            f"Unsafe path: {relative!r}")
    require(path.as_posix() == relative, f"Noncanonical path: {relative!r}")
    require(path.parts[0] not in GENERATED, f"Generated path in manifest: {relative}")
    return ROOT.joinpath(*path.parts)


def without_lean_comments(text):
    """Remove nested block/line comments, retaining strings and all other bytes.

    The resulting hash is an auxiliary comment-only change check, not a substitute
    for Lean parsing, typechecking, or the independent dependency gates.
    """
    out = []
    i = 0
    while i < len(text):
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while depth:
                require(i < len(text), "Unterminated Lean block comment")
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(text[start:i])
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def verify():
    require(__debug__, "Run Python without -O or -OO.")
    manifest = json.loads((ROOT / "PUBLICATION_MANIFEST.json").read_text())
    require(manifest["upstream_source_commit"] == PIN, "Unexpected upstream pin")
    expected = {"PUBLICATION_MANIFEST.json"}
    for entry in manifest["files"]:
        relative = entry["path"]
        require(relative not in expected, f"Duplicate manifest path: {relative}")
        expected.add(relative)
        path = safe_path(relative)
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular: {relative}")
        data = path.read_bytes()
        require(len(data) == entry["bytes"], f"Size mismatch: {relative}")
        require(digest(data) == entry["sha256"], f"Hash mismatch: {relative}")
    actual = set()
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if relative.parts[0] in GENERATED:
            continue
        require(not path.is_symlink(), f"Unexpected symlink: {relative}")
        if path.is_file():
            actual.add(relative.as_posix())
    require(actual == expected,
            f"File set mismatch: extra={sorted(actual-expected)}, missing={sorted(expected-actual)}")

    mapping = json.loads((ROOT / "provenance/SOURCE_MAP.json").read_text())
    require(mapping["upstream_source_commit"] == PIN, "Source-map pin mismatch")
    mapped = set()
    counts = {"project_source": 0, "build_configuration": 0, "independent_probe": 0}
    modified = 0
    for entry in mapping["files"]:
        relative = entry["public_path"]
        require(relative not in mapped, f"Duplicate mapped source: {relative}")
        mapped.add(relative)
        data = safe_path(relative).read_bytes()
        require(digest(data) == entry["public_sha256"], f"Source-map mismatch: {relative}")
        require(len(data) == entry["public_bytes"], f"Source-map size mismatch: {relative}")
        counts[entry["role"]] += 1
        if entry["change"] == "unchanged":
            require(entry["original_sha256"] == entry["public_sha256"],
                    f"Unchanged-source hash differs: {relative}")
            require(entry["original_bytes"] == len(data), f"Original size differs: {relative}")
        elif entry["change"] == "comment_only":
            require(relative.endswith(".lean"), f"Comment change on non-Lean file: {relative}")
            noncomment = without_lean_comments(data.decode("utf-8")).encode("utf-8")
            require(digest(noncomment) == entry["original_noncomment_sha256"],
                    f"Noncomment source mismatch: {relative}")
            modified += 1
        else:
            raise RuntimeError(f"Unsupported source change: {relative}")
    require(counts == {"project_source": 103, "build_configuration": 3,
                       "independent_probe": 6}, f"Unexpected source counts: {counts}")
    all_lean = {name for name in actual if name.endswith(".lean")}
    require(all_lean == {name for name in mapped if name.endswith(".lean")},
            "Unmapped or missing Lean source")
    library = {name for name in all_lean if name == "Karlin.lean" or name.startswith("Karlin/")}
    require(len(library) == 95, "Mathematical library source count differs")
    require({entry["source_path"] for entry in mapping["omitted_superseded_harnesses"]} == {
        "lean_formalization/faithful_audit/revised/RevisedGateAudit.lean",
        "lean_formalization/faithful_audit/revised/RevisedSevenGateAudit.lean"},
        "Unexpected superseded-harness omission ledger")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0",
            "Unexpected toolchain")
    require(digest((ROOT / "lake-manifest.json").read_bytes()) ==
            "035a626c8ad011ff3af79aabf71205ca0c6cbb83279e3cbaaff87c2f03f9f03d",
            "Dependency lockfile differs from upstream")
    print(f"PASS: {len(actual)} public files; 103 retained project Lean sources; six independent probes.")
    print("PASS: all 95 mathematical library sources retained; two superseded audit harnesses explicitly omitted.")
    print(f"PASS: {modified} comment-only source changes; other mapped files unchanged.")
    print("Integrity only: no build, mathematical, signature, or v19-correspondence claim.")


if __name__ == "__main__":
    try:
        verify()
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
