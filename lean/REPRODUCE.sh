#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
output=${1:-"$root/reproduction-output"}
if [[ -e "$output" ]]; then
  printf 'Refusing existing output directory: %s\n' "$output" >&2
  exit 1
fi
mkdir -p -- "$output"
output=$(cd -- "$output" && pwd)
cd -- "$root"
export KARLIN_REPRODUCTION_OUTPUT="$output"
status=failed
stage=package-integrity
finish() {
  exit_code=$?
  python3 - "$status" "$stage" "$exit_code" <<'PY'
import datetime, json, os, pathlib, sys
out = pathlib.Path(os.environ['KARLIN_REPRODUCTION_OUTPUT'])
result = {'status': sys.argv[1], 'last_stage': sys.argv[2],
          'exit_code': int(sys.argv[3]),
          'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'public-export integrity, pinned build/dependencies, six independent probes, eight companion checks',
          'not_checked': ['historical cross-revision preservation', 'complete v19 correspondence']}
(out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
PY
  return "$exit_code"
}
trap finish EXIT
python3 VERIFY_PACKAGE.py > "$output/package-before.log" 2>&1
stage=toolchain
command -v lake >/dev/null
lake env lean --version > "$output/lean-version.txt" 2>&1
grep -F 'version 4.27.0' "$output/lean-version.txt" >/dev/null

stage=clean-build
lake clean karlin_formalization > "$output/clean.log" 2>&1
lake build > "$output/build.log" 2>&1
stage=locked-dependencies
python3 - <<'PY' > "$output/dependency-check.json"
from pathlib import Path
import hashlib, json, subprocess
manifest = Path('lake-manifest.json')
if hashlib.sha256(manifest.read_bytes()).hexdigest() != '035a626c8ad011ff3af79aabf71205ca0c6cbb83279e3cbaaff87c2f03f9f03d':
    raise RuntimeError('Dependency lockfile changed')
results = []
for package in json.loads(manifest.read_text())['packages']:
    repo = Path('.lake/packages') / package['name']
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != package['rev']:
        raise RuntimeError('Dependency revision mismatch: ' + package['name'])
    status = subprocess.check_output(['git', '-C', str(repo), 'status', '--porcelain', '--untracked-files=no'], text=True)
    if status.strip():
        raise RuntimeError('Modified tracked dependency sources: ' + package['name'])
    results.append({'name': package['name'], 'rev': head, 'tracked_sources_clean': True})
print(json.dumps(results, indent=2))
PY
for probe in IndependentRemainingGate IndependentWholeGate IndependentContracts IndependentAssemblyGate IndependentRouteGate IndependentInventory; do
  stage="$probe"
  lake env lean "verification/probes/$probe.lean" > "$output/$probe.log" 2>&1
done
companions=(
  MainPaperRouteVerification.lean
  PaperRouteVerification.lean
  RemainingPaperRouteVerification.lean
  faithful_audit/IndependentMainDependencies.lean
  faithful_audit/FinalDependencies.lean
  faithful_audit/revised/RevisedAllDependencies.lean
  faithful_audit/revised/IntegrationGate.lean
  faithful_audit/revised/CrosswalkCurrentExports.lean
)
for companion in "${companions[@]}"; do
  stage="companion:$companion"
  lake env lean "$companion" > "$output/${companion//\//_}.log" 2>&1
done
stage=final-integrity
python3 VERIFY_PACKAGE.py > "$output/package-after.log" 2>&1
status=passed
stage=complete
printf 'PASS: source integrity, pinned build/dependencies, six independent probes, and eight companion checks.\nLogs: %s\n' "$output"
