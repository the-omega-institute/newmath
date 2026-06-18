#!/usr/bin/env bash
# Publish-gate regression ratchet: run the full suite but fail only on NEW
# failures relative to a committed baseline of known pre-existing failures
# (.publish-gate-baseline.txt). This unblocks publish on a suite that has
# pre-existing reds unrelated to each diff, while still catching real
# regressions the diff introduces.
#
# Portability + caching contract (do not reintroduce machine-specific paths
# or cache-busting flags):
#   * The script locates itself via BASH_SOURCE and runs pytest in its own
#     lab dir, so it works in any worktree and on any machine after a clone.
#   * Baseline is read relative to this script (committed alongside it).
#   * pytest runs with its normal cache enabled (no -p no:cacheprovider) and a
#     STABLE basetemp under a repo-relative tmp root, so .pytest_cache and
#     fixture tmp survive across runs and stay effective after switching
#     machines. Disk pressure is avoided by keeping tmp on the repo's disk
#     rather than /tmp.
#   * PYBIN defaults to python3; the host may inject a venv interpreter.
set +e
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lab_dir="$(cd "$script_dir/.." && pwd)"
repo_root="$(cd "$lab_dir/../.." && pwd)"
cd "$lab_dir"

PYBIN="${PYBIN:-python3}"
baseline_file="${PUBLISH_GATE_BASELINE:-$lab_dir/.publish-gate-baseline.txt}"

if [[ ! -f "$baseline_file" ]]; then
  echo "PUBLISH_GATE_ERROR: missing baseline file: $baseline_file" >&2
  exit 2
fi

# Stable, repo-relative tmp root so the pytest cache + fixture tmp persist
# across runs (effective caching) and stay on the repo's disk (no /tmp ENOSPC).
# Portable: derived from the repo root, never a hardcoded home path.
pytest_tmp_root="${PUBLISH_GATE_TMPDIR:-$repo_root/.pytest-tmp}"
mkdir -p "$pytest_tmp_root"
export TMPDIR="$pytest_tmp_root"

tmp_output="$(mktemp "$pytest_tmp_root/publish-gate-ratchet.XXXXXX")"
cleanup() {
  rm -f "$tmp_output"
}
trap cleanup EXIT

# Cache-friendly invocation: same shape as a normal `pytest -q` (which caches
# effectively), plus -rfE so failed/errored node-ids are listed for parsing.
# No --basetemp override and no -p no:cacheprovider, so caching stays effective.
"$PYBIN" -m pytest -q -rfE --tb=no "$@" > "$tmp_output" 2>&1
pytest_status=$?

"$PYBIN" - "$tmp_output" "$baseline_file" "$pytest_status" <<'PY'
import re
import sys
from pathlib import Path

output_path = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])
pytest_status = int(sys.argv[3])

text = output_path.read_text(encoding="utf-8", errors="replace")
lines = text.splitlines()

if not lines:
    print("PUBLISH_GATE_ERROR: pytest produced no output; failing closed", file=sys.stderr)
    sys.exit(2)

lower_text = text.lower()
if "no tests ran" in lower_text or "no tests collected" in lower_text:
    print("PUBLISH_GATE_ERROR: pytest did not collect tests; failing closed", file=sys.stderr)
    sys.exit(2)

summary_seen = any(
    re.search(r"\b(?:passed|failed|error|errors|skipped|xfailed|xpassed)\b", line)
    and (" in " in line or line.startswith("="))
    for line in lines[-100:]
)
if not summary_seen and pytest_status not in (0, 1):
    print(
        f"PUBLISH_GATE_ERROR: pytest did not complete normally (exit {pytest_status}); failing closed",
        file=sys.stderr,
    )
    sys.exit(2)

def parse_node_ids(source_lines):
    node_ids = set()
    for line in source_lines:
        if line.startswith("FAILED "):
            node_id = line[len("FAILED ") :]
        elif line.startswith("ERROR "):
            node_id = line[len("ERROR ") :]
        else:
            continue
        node_id = node_id.split(" - ", 1)[0].strip()
        if node_id:
            node_ids.add(node_id)
    return node_ids

current = parse_node_ids(lines)
baseline = {
    line.strip()
    for line in baseline_path.read_text(encoding="utf-8").splitlines()
    if line.strip() and not line.lstrip().startswith("#")
}

if not baseline:
    print("PUBLISH_GATE_ERROR: baseline is empty; failing closed", file=sys.stderr)
    sys.exit(2)

if pytest_status not in (0, 1) and not current:
    print(
        f"PUBLISH_GATE_ERROR: pytest exited {pytest_status} without parseable failing node ids; failing closed",
        file=sys.stderr,
    )
    sys.exit(2)

new = sorted(current - baseline)
fixed = sorted(baseline - current)

if new:
    print(f"PUBLISH_GATE_FAIL: {len(new)} new failing test(s):")
    for node_id in new:
        print(node_id)
    if fixed:
        print(f"PUBLISH_GATE_INFO: {len(fixed)} baseline test(s) not currently failing:")
        for node_id in fixed:
            print(node_id)
    sys.exit(1)

print(f"PUBLISH_GATE_OK: current_failures={len(current)} baseline={len(baseline)} new=0")
if fixed:
    print(f"PUBLISH_GATE_INFO: {len(fixed)} baseline test(s) not currently failing:")
    for node_id in fixed:
        print(node_id)
sys.exit(0)
PY
