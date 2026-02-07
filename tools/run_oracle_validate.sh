#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Run `tvm-lean-oracle-validate` per-instruction in parallel and store logs.

Defaults:
  --jobs 12
  --variants 20 --code-variants 8 --cases 20 --max-nosig-depth 64 --min-cases 10
  --random-cases 64 --seed 1

Examples:
  tools/run_oracle_validate.sh --limit 50
  tools/run_oracle_validate.sh --only ADDINT --verbose
  tools/run_oracle_validate.sh --variants 64 --code-variants 64 --cases auto
  tools/run_oracle_validate.sh --jobs 12 --out oracle/_runs/latest

Env overrides (optional):
  TON_FIFT_BIN=/Users/daniil/Coding/ton/build/crypto/fift
  TON_FIFT_LIB=/Users/daniil/Coding/ton/crypto/fift/lib
  TVMLEANTON_ORACLE_FIF=tools/ton_oracle_runvm.fif
  TVMLEANTON_ORACLE_LIB_FIF=tools/ton_oracle_runvm_lib.fif
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ROOT}/.lake/build/bin/tvm-lean-oracle-validate"
IDX="${ROOT}/docs/progress/tvm_spec_index.json"

JOBS=12
LIMIT=0
ONLY=""
VARIANTS=20
CODE_VARIANTS=8
CASES="20"
MAX_NOSIG_DEPTH=64
MIN_CASES=10
RANDOM_CASES=64
SEED=1
VERBOSE=0
OUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --limit) LIMIT="$2"; shift 2 ;;
    --only) ONLY="$2"; shift 2 ;;
    --variants) VARIANTS="$2"; shift 2 ;;
    --code-variants) CODE_VARIANTS="$2"; shift 2 ;;
    --cases) CASES="$2"; shift 2 ;;
    --max-nosig-depth) MAX_NOSIG_DEPTH="$2"; shift 2 ;;
    --min-cases) MIN_CASES="$2"; shift 2 ;;
    --random-cases) RANDOM_CASES="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --verbose) VERBOSE=1; shift ;;
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
  OUT="${ROOT}/oracle/_runs/${ts}"
fi

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
else
  if ! is_uint "$CASES"; then
    echo "invalid --cases: $CASES (expected Nat or 'auto')" >&2
    exit 2
  fi
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
if ! is_uint "$SEED"; then
  echo "invalid --seed: $SEED" >&2
  exit 2
fi
if (( CASES < MIN_CASES )); then
  echo "--cases must be >= --min-cases (cases=$CASES min-cases=$MIN_CASES)" >&2
  exit 2
fi

mkdir -p "$OUT/logs" "$OUT/ok" "$OUT/fail"

if [[ ! -x "$BIN" ]]; then
  (cd "$ROOT" && lake build tvm-lean-oracle-validate)
fi

cd "$ROOT"

names_file="${OUT}/names.txt"
if [[ -n "$ONLY" ]]; then
  printf '%s\n' "$ONLY" >"$names_file"
else
  python3 - <<'PY' "$IDX" "$LIMIT" >"$names_file"
import json, sys
idx_path, limit_s = sys.argv[1], sys.argv[2]
limit = int(limit_s) if limit_s else 0
with open(idx_path) as f:
    idx = json.load(f)
names = [row["name"] for row in idx["tvm_instructions"]]
if limit > 0:
    names = names[:limit]
for n in names:
    print(n)
PY
fi

export ORACLE_RUN_DIR="$OUT"
export ORACLE_BIN="$BIN"
export ORACLE_VARIANTS="$VARIANTS"
export ORACLE_CODE_VARIANTS="$CODE_VARIANTS"
export ORACLE_CASES="$CASES"
export ORACLE_MAX_NOSIG_DEPTH="$MAX_NOSIG_DEPTH"
export ORACLE_MIN_CASES="$MIN_CASES"
export ORACLE_RANDOM_CASES="$RANDOM_CASES"
export ORACLE_SEED="$SEED"
export ORACLE_VERBOSE="$VERBOSE"
export ORACLE_PROGRESS_FILE="${OUT}/progress.log"

echo "run_dir: $OUT"
echo "config: jobs=${JOBS} variants=${ORACLE_VARIANTS} code_variants=${ORACLE_CODE_VARIANTS} cases=${ORACLE_CASES} min_cases=${ORACLE_MIN_CASES} random_cases=${ORACLE_RANDOM_CASES} seed=${ORACLE_SEED}"
echo "progress_log: ${ORACLE_PROGRESS_FILE}"

cat "$names_file" | xargs -n 1 -P "$JOBS" bash -lc '
  set -euo pipefail
  name="$1"
  safe="$(printf '%s' "$name" | tr -c "A-Za-z0-9._-" "_" )"
  log="${ORACLE_RUN_DIR}/logs/${safe}.log"
  ok="${ORACLE_RUN_DIR}/ok/${safe}"
  fail="${ORACLE_RUN_DIR}/fail/${safe}"
  rm -f "$ok" "$fail"
  start_ts="$(date +%s)"
  {
    echo "name: $name"
    echo "variants: ${ORACLE_VARIANTS}  code-variants: ${ORACLE_CODE_VARIANTS}  cases: ${ORACLE_CASES}  max-nosig-depth: ${ORACLE_MAX_NOSIG_DEPTH}  min-cases: ${ORACLE_MIN_CASES}  random-cases: ${ORACLE_RANDOM_CASES}  seed: ${ORACLE_SEED}"
    echo
    args=(--only "$name" --variants "$ORACLE_VARIANTS" --code-variants "$ORACLE_CODE_VARIANTS" --cases "$ORACLE_CASES" --max-nosig-depth "$ORACLE_MAX_NOSIG_DEPTH" --min-cases "$ORACLE_MIN_CASES" --random-cases "$ORACLE_RANDOM_CASES" --seed "$ORACLE_SEED")
    if [[ "${ORACLE_VERBOSE}" -eq 1 ]]; then
      args+=(--verbose)
    fi
    "${ORACLE_BIN}" "${args[@]}"
  } >"$log" 2>&1 && {
    touch "$ok"
    end_ts="$(date +%s)"
    dt="$((end_ts - start_ts))"
    line="PASS ${name} (${dt}s)"
    echo "$line"
    printf "%s\t%s\t%s\n" "pass" "$name" "$dt" >> "${ORACLE_PROGRESS_FILE}"
  } || {
    touch "$fail"
    end_ts="$(date +%s)"
    dt="$((end_ts - start_ts))"
    line="FAIL ${name} (${dt}s) log=${log}"
    echo "$line"
    printf "%s\t%s\t%s\n" "fail" "$name" "$dt" >> "${ORACLE_PROGRESS_FILE}"
    exit 0
  }
' _

python3 - <<'PY' "$OUT"
import json, os, sys

run_dir = sys.argv[1]
ok_dir = os.path.join(run_dir, "ok")
fail_dir = os.path.join(run_dir, "fail")
ok = sorted(os.listdir(ok_dir)) if os.path.isdir(ok_dir) else []
fail = sorted(os.listdir(fail_dir)) if os.path.isdir(fail_dir) else []
summary = {
    "total": len(ok) + len(fail),
    "pass": len(ok),
    "fail": len(fail),
    "failures": fail,
}
out_path = os.path.join(run_dir, "summary.json")
with open(out_path, "w") as f:
    json.dump(summary, f, indent=2, sort_keys=True)
print(f"run_dir: {run_dir}")
print(f"summary: {out_path}")
pct = 0.0 if summary["total"] == 0 else (summary["pass"] * 100.0 / summary["total"])
print(f"total={summary['total']} pass={summary['pass']} fail={summary['fail']} pass_pct={pct:.1f}%")
if fail:
    print("first_failures:")
    for n in fail[:20]:
        print("  -", n)
PY

if [[ -n "$(ls -A "$OUT/fail" 2>/dev/null || true)" ]]; then
  exit 1
fi
exit 0
