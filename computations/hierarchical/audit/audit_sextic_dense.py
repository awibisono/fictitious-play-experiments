if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

import sys, json, time, hashlib
from pathlib import Path

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
H = HERE.parent
sys.path.insert(0, str(HERE))
from audit_replay_outputs import run

begin = time.monotonic()
src = H / "order6_recursive_replay.json"
p = H / "order6_dense_certified_samples.json"
base = json.loads(src.read_text())
dense = json.loads(p.read_text())
Q = int(base["Q"])
assert (
    dense["coverage_source"] == src.name
    and dense["coverage_source_sha256"] == hashlib.sha256(src.read_bytes()).hexdigest()
)
assert dense["engine_sha256"] == base["engine_sha256"]
assert [int(r["q"]) for r in dense["samples"]] == [Q, Q + 1] + [
    Q * 2**j for j in range(1, 13)
]
for r in dense["samples"]:
    assert Q <= int(r["q"]) <= 4096 * Q
base["samples"] = dense["samples"]
out = run(6, base)
out.update(
    status="PASS_INDEPENDENT_DENSE_EXTRACTION",
    samples_are_prefixes_of_certified_word=True,
    dense_file_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    seconds=time.monotonic() - begin,
)
(HERE / "sextic_dense_audit_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
