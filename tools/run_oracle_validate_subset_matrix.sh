#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Run tvm-lean-oracle-validate for a subset of instruction names across a seed matrix.

Required:
  --names-file <path>   file with one instruction name per line

Defaults:
  --seeds 1,7,42
  --jobs 12
  --variants 20 --code-variants 8 --cases 20 --max-nosig-depth 64 --min-cases 10
  --random-cases 64

Examples:
  tools/run_oracle_validate_subset_matrix.sh \
    --names-file oracle/runs/hot_names_from_history.txt \
    --seeds 42,1337,7 \
    --variants 260 --code-variants 520 --cases 260 --random-cases 12288
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ROOT}/.lake/build/bin/tvm-lean-oracle-validate"

NAMES_FILE=""
SEEDS_CSV="1,7,42"
JOBS=12
VARIANTS=20
CODE_VARIANTS=8
CASES=20
MAX_NOSIG_DEPTH=64
MIN_CASES=10
RANDOM_CASES=64
VERBOSE=0
OUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --names-file)
      NAMES_FILE="$2"
      shift 2
      ;;
    --seeds)
      SEEDS_CSV="$2"
      shift 2
      ;;
    --jobs)
      JOBS="$2"
      shift 2
      ;;
    --variants)
      VARIANTS="$2"
      shift 2
      ;;
    --code-variants)
      CODE_VARIANTS="$2"
      shift 2
      ;;
    --cases)
      CASES="$2"
      shift 2
      ;;
    --max-nosig-depth)
      MAX_NOSIG_DEPTH="$2"
      shift 2
      ;;
    --min-cases)
      MIN_CASES="$2"
      shift 2
      ;;
    --random-cases)
      RANDOM_CASES="$2"
      shift 2
      ;;
    --verbose)
      VERBOSE=1
      shift
      ;;
    --out)
      OUT="$2"
      shift 2
      ;;
    *)
      echo "unknown arg: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ -z "$NAMES_FILE" ]]; then
  echo "--names-file is required" >&2
  exit 2
fi
if [[ ! -f "$NAMES_FILE" ]]; then
  echo "names file not found: $NAMES_FILE" >&2
  exit 2
fi

if [[ -z "$OUT" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  OUT="${ROOT}/oracle/runs/subset_matrix_${ts}"
fi
mkdir -p "$OUT"

if [[ ! -x "$BIN" ]]; then
  (cd "$ROOT" && lake build tvm-lean-oracle-validate)
fi

cd "$ROOT"

IFS=',' read -r -a SEEDS <<< "$SEEDS_CSV"
if [[ "${#SEEDS[@]}" -eq 0 ]]; then
  echo "no seeds provided" >&2
  exit 2
fi

FAIL_ANY=0
RUN_DIRS=()

for seed_raw in "${SEEDS[@]}"; do
  seed="$(echo "$seed_raw" | xargs)"
  if [[ -z "$seed" ]]; then
    continue
  fi
  run="${OUT}/seed_${seed}"
  mkdir -p "$run/logs" "$run/ok" "$run/fail"
  sed '/^[[:space:]]*$/d; /^[[:space:]]*#/d' "$NAMES_FILE" > "$run/names.txt"

  echo "=== seed ${seed} ==="

  xargs -P "$JOBS" -I{} bash -lc '
    set -euo pipefail
    name="$1"; run="$2"; seed="$3"; bin="$4"
    variants="$5"; code_variants="$6"; cases="$7"
    max_no_sig="$8"; min_cases="$9"; random_cases="${10}"; verbose="${11}"

    safe="$(printf "%s" "$name" | tr -c "A-Za-z0-9._-" "_")"
    log="${run}/logs/${safe}.log"
    ok="${run}/ok/${safe}"
    fail="${run}/fail/${safe}"
    rm -f "$ok" "$fail"

    args=(
      --only "$name"
      --variants "$variants"
      --code-variants "$code_variants"
      --cases "$cases"
      --max-nosig-depth "$max_no_sig"
      --min-cases "$min_cases"
      --random-cases "$random_cases"
      --seed "$seed"
    )
    if [[ "$verbose" -eq 1 ]]; then
      args+=(--verbose)
    fi

    if "$bin" "${args[@]}" >"$log" 2>&1; then
      touch "$ok"
    else
      touch "$fail"
    fi
  ' _ '{}' "$run" "$seed" "$BIN" "$VARIANTS" "$CODE_VARIANTS" "$CASES" "$MAX_NOSIG_DEPTH" "$MIN_CASES" "$RANDOM_CASES" "$VERBOSE" < "$run/names.txt"

  python3 - <<'PY' "$run"
import json
import os
import sys

run = sys.argv[1]
ok = sorted(os.listdir(run + "/ok"))
fail = sorted(os.listdir(run + "/fail"))
summary = {
    "total": len(ok) + len(fail),
    "pass": len(ok),
    "fail": len(fail),
    "failures": fail,
}
with open(run + "/summary.json", "w") as f:
    json.dump(summary, f, indent=2, sort_keys=True)
print(run, summary)
PY

  if [[ -n "$(ls -A "$run/fail" 2>/dev/null || true)" ]]; then
    FAIL_ANY=1
  fi
  RUN_DIRS+=("$run")
done

python3 - <<'PY' "$OUT" "${RUN_DIRS[@]}"
import json
import os
import sys

out = sys.argv[1]
runs = sys.argv[2:]
matrix = {
    "runs": [],
    "total_runs": 0,
    "all_passed": True,
    "union_failures": [],
}
union = set()

for run in runs:
  p = os.path.join(run, "summary.json")
  row = {"run_dir": run, "summary_path": p}
  if os.path.isfile(p):
    s = json.load(open(p))
    row.update({
      "total": s.get("total", 0),
      "pass": s.get("pass", 0),
      "fail": s.get("fail", 0),
      "failures": s.get("failures", []),
    })
    if row["fail"] > 0:
      matrix["all_passed"] = False
      union.update(row["failures"])
  else:
    row.update({
      "total": 0,
      "pass": 0,
      "fail": -1,
      "failures": ["missing_summary"],
    })
    matrix["all_passed"] = False
    union.add("missing_summary")
  matrix["runs"].append(row)

matrix["total_runs"] = len(matrix["runs"])
matrix["union_failures"] = sorted(union)
out_path = os.path.join(out, "matrix_summary.json")
with open(out_path, "w") as f:
  json.dump(matrix, f, indent=2, sort_keys=True)
print(f"matrix_summary: {out_path}")
print(f"total_runs={matrix['total_runs']} all_passed={matrix['all_passed']}")
if matrix["union_failures"]:
  print("union_failures:")
  for n in matrix["union_failures"]:
    print(f"  - {n}")
PY

if [[ "$FAIL_ANY" -ne 0 ]]; then
  exit 1
fi
exit 0
