#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Run multiple oracle-validate sweeps across a seed matrix and aggregate results.

Defaults:
  --seeds 1,7,42
  (all other flags are forwarded to tools/run_oracle_validate.sh)

Examples:
  tools/run_oracle_validate_matrix.sh --seeds 4040,9001,1337 --variants 220 --code-variants 64 --cases 1024
  tools/run_oracle_validate_matrix.sh --seeds 1,7,42 --variants 64 --code-variants 64 --cases auto
  tools/run_oracle_validate_matrix.sh --seeds 1,2,3 --limit 200 --out oracle/_runs/matrix_smoke
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUN_ONE="${ROOT}/tools/run_oracle_validate.sh"

SEEDS_CSV="1,7,42"
OUT=""
FORWARD_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --seeds)
      SEEDS_CSV="$2"
      shift 2
      ;;
    --out)
      OUT="$2"
      shift 2
      ;;
    *)
      FORWARD_ARGS+=("$1")
      shift
      ;;
  esac
done

if [[ -z "$OUT" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  OUT="${ROOT}/oracle/_runs/matrix_${ts}"
fi
mkdir -p "$OUT"

IFS=',' read -r -a SEEDS <<< "$SEEDS_CSV"
if [[ "${#SEEDS[@]}" -eq 0 ]]; then
  echo "no seeds provided" >&2
  exit 2
fi

RUN_DIRS=()
FAIL_ANY=0

for seed_raw in "${SEEDS[@]}"; do
  seed="$(echo "$seed_raw" | xargs)"
  if [[ -z "$seed" ]]; then
    continue
  fi
  run_out="${OUT}/seed_${seed}"
  echo "=== seed ${seed} ==="
  if "$RUN_ONE" "${FORWARD_ARGS[@]}" --seed "$seed" --out "$run_out"; then
    echo "seed ${seed}: PASS"
  else
    echo "seed ${seed}: FAIL"
    FAIL_ANY=1
  fi
  RUN_DIRS+=("$run_out")
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

for run_dir in runs:
    summary_path = os.path.join(run_dir, "summary.json")
    row = {
        "run_dir": run_dir,
        "summary_path": summary_path,
    }
    if os.path.isfile(summary_path):
        with open(summary_path) as f:
            s = json.load(f)
        row.update({
            "total": s.get("total", 0),
            "pass": s.get("pass", 0),
            "fail": s.get("fail", 0),
            "failures": s.get("failures", []),
        })
        if row["fail"] > 0:
            matrix["all_passed"] = False
            for n in row["failures"]:
                union.add(n)
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
