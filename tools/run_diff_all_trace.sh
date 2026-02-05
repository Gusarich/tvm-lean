#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  tools/run_diff_all_trace.sh [KEY=VALUE ...]

Runs `tvm-lean-diff-test` over all JSON fixtures in parallel shards, writing:
  - per-shard reports: <OUT_BASE>_shard<i>.json
  - merged report:     <OUT_BASE>.json

Keys (can be passed as env vars or as KEY=VALUE arguments):
  DIR=diff-test/fixtures        Fixtures directory
  J=12                         Number of shards (parallel workers)
  TRACE_MAX=200                 Max trace entries per failing case
  PROGRESS_EVERY=200            Progress print interval per shard
  SKIP_UNSUPPORTED=1            1 to enable --skip-unsupported, 0 to disable
  NO_BUILD=0                    1 to skip `lake build tvm-lean-diff-test`
  RUN_ID=YYYYMMDD_HHMMSS        Included in default OUT_BASE
  OUT_BASE=diff-test/_report... Output base path (no extension)

Examples:
  tools/run_diff_all_trace.sh
  tools/run_diff_all_trace.sh J=12 TRACE_MAX=200
  DIR=diff-test/fixtures J=12 tools/run_diff_all_trace.sh
  OUT_BASE=diff-test/_report_all_trace_my_run tools/run_diff_all_trace.sh
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

for arg in "$@"; do
  case "$arg" in
    DIR=*) DIR="${arg#DIR=}" ;;
    J=*) J="${arg#J=}" ;;
    TRACE_MAX=*) TRACE_MAX="${arg#TRACE_MAX=}" ;;
    PROGRESS_EVERY=*) PROGRESS_EVERY="${arg#PROGRESS_EVERY=}" ;;
    SKIP_UNSUPPORTED=*) SKIP_UNSUPPORTED="${arg#SKIP_UNSUPPORTED=}" ;;
    NO_BUILD=*) NO_BUILD="${arg#NO_BUILD=}" ;;
    RUN_ID=*) RUN_ID="${arg#RUN_ID=}" ;;
    OUT_BASE=*) OUT_BASE="${arg#OUT_BASE=}" ;;
    *)
      echo "error: unknown argument '$arg'" >&2
      usage >&2
      exit 2
      ;;
  esac
done

DIR="${DIR:-diff-test/fixtures}"
J="${J:-12}"
TRACE_MAX="${TRACE_MAX:-200}"
PROGRESS_EVERY="${PROGRESS_EVERY:-200}"
SKIP_UNSUPPORTED="${SKIP_UNSUPPORTED:-1}"
NO_BUILD="${NO_BUILD:-0}"

RUN_ID="${RUN_ID:-$(date +%Y%m%d_%H%M%S)}"
OUT_BASE="${OUT_BASE:-diff-test/_report_all_trace_${RUN_ID}}"

if [[ "$NO_BUILD" != "1" ]]; then
  lake build tvm-lean-diff-test
fi

BIN="./.lake/build/bin/tvm-lean-diff-test"
if [[ ! -x "$BIN" ]]; then
  echo "error: missing binary '$BIN' (build failed?)" >&2
  exit 2
fi

if [[ "$J" -le 0 ]]; then
  echo "error: J must be > 0 (got '$J')" >&2
  exit 2
fi

echo "Running diff-test shards: J=$J dir='$DIR' trace_max=$TRACE_MAX progress_every=$PROGRESS_EVERY"
echo "Output base: $OUT_BASE"

pids=()
for i in $(seq 0 $((J - 1))); do
  out="${OUT_BASE}_shard${i}.json"
  args=(--dir "$DIR" --shard "$i" --shards "$J" --out "$out" --progress-every "$PROGRESS_EVERY" --trace-failures --trace-max "$TRACE_MAX")
  if [[ "$SKIP_UNSUPPORTED" == "1" ]]; then
    args+=(--skip-unsupported)
  fi
  "$BIN" "${args[@]}" &
  pids+=("$!")
done

failed=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    failed=1
  fi
done

python3 - <<PY
import glob, json
out = []
paths = sorted(glob.glob("${OUT_BASE}_shard*.json"))
for p in paths:
    with open(p) as f:
        out.extend(json.load(f))
status = {}
for r in out:
    s = r.get("status")
    status[s] = status.get(s, 0) + 1
final_path = "${OUT_BASE}.json"
with open(final_path, "w") as f:
    json.dump(out, f, indent=2)
print("merged", len(out), "results ->", final_path)
print("status counts:", status)
PY

if [[ "$failed" == "1" ]]; then
  echo "warning: at least one shard exited non-zero (partial report still written)" >&2
  exit 1
fi
