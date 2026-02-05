#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Run `tvm-lean-diff-test` in parallel shards and store JSON results + logs.

Defaults:
  --dir diff-test/fixtures
  --shards 12
  --trace-failures --trace-max 200
  --fuel 1000000 --gas-limit 1000000
  --progress-every 200

Examples:
  tools/run_diff_tests.sh --max-cases 100
  tools/run_diff_tests.sh --dir diff-test/fixtures --shards 12 --out diff-test/_runs/latest
  tools/run_diff_tests.sh --dir diff-test/fixtures --shards 12 --trace-all --trace-max 50

Notes:
  - `--max-cases N` is applied globally by creating a symlink subset directory.
  - Outputs:
      <out>/shard_*.json  per-shard JSON arrays
      <out>/shard_*.log   per-shard logs (progress + trace)
      <out>/merged.json   merged JSON array
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ROOT}/.lake/build/bin/tvm-lean-diff-test"

DIR="${ROOT}/diff-test/fixtures"
SHARDS=12
MAX_CASES=0
FUEL=1000000
GAS_LIMIT=1000000
TRACE_FAILURES=1
TRACE_ALL=0
TRACE_MAX=200
PROGRESS_EVERY=200
SKIP_UNSUPPORTED=0
STRICT_EXIT=0
OUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --dir) DIR="$2"; shift 2 ;;
    --shards) SHARDS="$2"; shift 2 ;;
    --max-cases) MAX_CASES="$2"; shift 2 ;;
    --fuel) FUEL="$2"; shift 2 ;;
    --gas-limit) GAS_LIMIT="$2"; shift 2 ;;
    --trace-max) TRACE_MAX="$2"; shift 2 ;;
    --trace-all) TRACE_ALL=1; shift ;;
    --trace-failures) TRACE_FAILURES=1; shift ;;
    --no-trace-failures) TRACE_FAILURES=0; shift ;;
    --progress-every) PROGRESS_EVERY="$2"; shift 2 ;;
    --skip-unsupported) SKIP_UNSUPPORTED=1; shift ;;
    --strict-exit) STRICT_EXIT=1; shift ;;
    --out) OUT="$2"; shift 2 ;;
    *)
      echo "unknown arg: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ -z "$OUT" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  OUT="${ROOT}/diff-test/_runs/${ts}"
fi

mkdir -p "$OUT"

if [[ ! -x "$BIN" ]]; then
  (cd "$ROOT" && lake build tvm-lean-diff-test)
fi

RUN_DIR="$OUT"
SUBSET_DIR="$DIR"
if [[ "$MAX_CASES" -gt 0 ]]; then
  SUBSET_DIR="${RUN_DIR}/subset_${MAX_CASES}"
  rm -rf "$SUBSET_DIR"
  mkdir -p "$SUBSET_DIR"

  python3 - <<'PY' "$DIR" "$SUBSET_DIR" "$MAX_CASES"
import os, sys

root_dir, subset_dir, max_cases_s = sys.argv[1], sys.argv[2], sys.argv[3]
max_cases = int(max_cases_s)

def is_json_fixture(path: str) -> bool:
    base = os.path.basename(path)
    if not base.endswith(".json"):
        return False
    if base.startswith("_"):
        return False
    parts = path.split(os.sep)
    return not any(seg.startswith("_") for seg in parts)

files = []
for base, _dirs, names in os.walk(root_dir):
    for n in names:
        p = os.path.join(base, n)
        if is_json_fixture(p):
            files.append(p)

files.sort()
sel = files[:max_cases]
for i, p in enumerate(sel):
    link_name = f"{i:05d}_" + os.path.basename(p)
    dst = os.path.join(subset_dir, link_name)
    os.symlink(os.path.abspath(p), dst)

print(f"subset: selected {len(sel)}/{len(files)} fixtures into {subset_dir}")
PY
fi

if [[ "$SHARDS" -lt 1 ]]; then
  echo "--shards must be >= 1" >&2
  exit 2
fi

echo "run_dir: $RUN_DIR"
echo "fixtures_dir: $SUBSET_DIR"
echo "shards: $SHARDS"

pids=()
for ((i=0; i<SHARDS; i++)); do
  out_json="${RUN_DIR}/shard_${i}.json"
  out_log="${RUN_DIR}/shard_${i}.log"
  args=(--dir "$SUBSET_DIR" --shards "$SHARDS" --shard "$i" --fuel "$FUEL" --gas-limit "$GAS_LIMIT" --trace-max "$TRACE_MAX" --out "$out_json")
  if [[ "$TRACE_ALL" -eq 1 ]]; then
    args+=(--trace-all)
  elif [[ "$TRACE_FAILURES" -eq 1 ]]; then
    args+=(--trace-failures)
  fi
  if [[ "$PROGRESS_EVERY" -gt 0 ]]; then
    args+=(--progress-every "$PROGRESS_EVERY")
  fi
  if [[ "$SKIP_UNSUPPORTED" -eq 1 ]]; then
    args+=(--skip-unsupported)
  fi
  if [[ "$STRICT_EXIT" -eq 1 ]]; then
    args+=(--strict-exit)
  fi

  ( "$BIN" "${args[@]}" >"$out_log" 2>&1 ) &
  pids+=("$!")
done

rc=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    rc=1
  fi
done

python3 - <<'PY' "$RUN_DIR"
import json, os, sys
from collections import Counter

run_dir = sys.argv[1]
merged = []
for name in sorted(os.listdir(run_dir)):
    if not name.startswith("shard_") or not name.endswith(".json"):
        continue
    path = os.path.join(run_dir, name)
    if os.path.getsize(path) == 0:
        continue
    with open(path) as f:
        merged.extend(json.load(f))

out_path = os.path.join(run_dir, "merged.json")
with open(out_path, "w") as f:
    json.dump(merged, f, indent=2, sort_keys=True)

statuses = Counter(r.get("status") for r in merged)
total = len(merged)
pass_n = statuses.get("PASS", 0)
fail_n = statuses.get("FAIL", 0)
skip_n = statuses.get("SKIP", 0)
err_n = statuses.get("ERROR", 0)
pass_pct = 0.0 if total == 0 else (100.0 * pass_n / total)
print(f"merged: {out_path}")
print(f"total={total} pass={pass_n} fail={fail_n} skip={skip_n} error={err_n} pass%={pass_pct:.2f}%")
PY

exit "$rc"

