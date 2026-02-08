#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Run an extensive all-instruction Lean-vs-Fift oracle parity matrix.

This is a bounded-exhaustive + randomized stress suite:
- all instruction names from docs/progress/tvm_spec_index.json
- strict parity checks (exit, gas, c4/c5 hashes, stack canonicalization)
- multi-seed matrix to increase coverage diversity

Defaults:
  --seeds 1,7,42,1337
  --jobs 12
  --variants 32
  --code-variants 32
  --cases auto          # resolves to variants * code-variants
  --max-nosig-depth 96
  --min-cases 32
  --random-cases 2048

Examples:
  tools/run_oracle_validate_extensive.sh
  tools/run_oracle_validate_extensive.sh --jobs 24 --variants 128 --code-variants 128
  tools/run_oracle_validate_extensive.sh --limit 200 --out oracle/runs/extensive_smoke
  tools/run_oracle_validate_extensive.sh --only ADDINT --seeds 1,2,3 --verbose
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUN_MATRIX="${ROOT}/tools/run_oracle_validate_matrix.sh"

SEEDS="1,7,42,1337"
JOBS=12
VARIANTS=32
CODE_VARIANTS=32
CASES="auto"
MAX_NOSIG_DEPTH=96
MIN_CASES=32
RANDOM_CASES=2048
LIMIT=0
ONLY=""
VERBOSE=0
OUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --seeds)
      SEEDS="$2"
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
    --limit)
      LIMIT="$2"
      shift 2
      ;;
    --only)
      ONLY="$2"
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

is_uint() {
  [[ "$1" =~ ^[0-9]+$ ]]
}

if ! is_uint "$JOBS"; then
  echo "invalid --jobs: $JOBS" >&2
  exit 2
fi
if ! is_uint "$VARIANTS"; then
  echo "invalid --variants: $VARIANTS" >&2
  exit 2
fi
if ! is_uint "$CODE_VARIANTS"; then
  echo "invalid --code-variants: $CODE_VARIANTS" >&2
  exit 2
fi
if [[ "$CASES" == "auto" ]]; then
  CASES="$((VARIANTS * CODE_VARIANTS))"
elif ! is_uint "$CASES"; then
  echo "invalid --cases: $CASES (expected Nat or 'auto')" >&2
  exit 2
fi
if ! is_uint "$MAX_NOSIG_DEPTH"; then
  echo "invalid --max-nosig-depth: $MAX_NOSIG_DEPTH" >&2
  exit 2
fi
if ! is_uint "$MIN_CASES"; then
  echo "invalid --min-cases: $MIN_CASES" >&2
  exit 2
fi
if ! is_uint "$RANDOM_CASES"; then
  echo "invalid --random-cases: $RANDOM_CASES" >&2
  exit 2
fi
if ! is_uint "$LIMIT"; then
  echo "invalid --limit: $LIMIT" >&2
  exit 2
fi
if (( CASES < MIN_CASES )); then
  echo "--cases must be >= --min-cases (cases=$CASES min-cases=$MIN_CASES)" >&2
  exit 2
fi

if [[ -z "$OUT" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  OUT="${ROOT}/oracle/runs/extensive_${ts}"
fi
mkdir -p "$OUT"

echo "suite_out: $OUT"
echo "config: seeds=${SEEDS} jobs=${JOBS} variants=${VARIANTS} code_variants=${CODE_VARIANTS} cases=${CASES} max_nosig_depth=${MAX_NOSIG_DEPTH} min_cases=${MIN_CASES} random_cases=${RANDOM_CASES}"

args=(
  --seeds "$SEEDS"
  --out "$OUT"
  --jobs "$JOBS"
  --variants "$VARIANTS"
  --code-variants "$CODE_VARIANTS"
  --cases "$CASES"
  --max-nosig-depth "$MAX_NOSIG_DEPTH"
  --min-cases "$MIN_CASES"
  --random-cases "$RANDOM_CASES"
)
if (( LIMIT > 0 )); then
  args+=(--limit "$LIMIT")
fi
if [[ -n "$ONLY" ]]; then
  args+=(--only "$ONLY")
fi
if (( VERBOSE == 1 )); then
  args+=(--verbose)
fi

"$RUN_MATRIX" "${args[@]}"

python3 - <<'PY' "$OUT" "$SEEDS" "$JOBS" "$VARIANTS" "$CODE_VARIANTS" "$CASES" "$MAX_NOSIG_DEPTH" "$MIN_CASES" "$RANDOM_CASES" "$LIMIT" "$ONLY" "$VERBOSE"
import json
import os
import sys

(
    out,
    seeds,
    jobs,
    variants,
    code_variants,
    cases,
    max_nosig_depth,
    min_cases,
    random_cases,
    limit,
    only,
    verbose,
) = sys.argv[1:]

cfg = {
    "seeds": seeds,
    "jobs": int(jobs),
    "variants": int(variants),
    "code_variants": int(code_variants),
    "cases": int(cases),
    "max_nosig_depth": int(max_nosig_depth),
    "min_cases": int(min_cases),
    "random_cases": int(random_cases),
    "limit": int(limit),
    "only": only,
    "verbose": verbose == "1",
}

path = os.path.join(out, "suite_config.json")
with open(path, "w") as f:
    json.dump(cfg, f, indent=2, sort_keys=True)
print(f"suite_config: {path}")
print(f"matrix_summary: {os.path.join(out, 'matrix_summary.json')}")
PY

exit 0
