#!/usr/bin/env python3
"""
Pretty-print tvm-lean diff-test results with VM traces.

Reads the JSONL file produced by `diff-test/collector sweep --run-lean --trace-failures`
and prints per-tx opcode/event + stack transitions.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any, Dict, Iterable, List, Optional, Set


def _load_results(path: str) -> Iterable[Dict[str, Any]]:
    """
    Load either:
      - JSONL: one object per line
      - JSON array: `[ {...}, {...} ]` (small files only)
    """
    with open(path, "r", encoding="utf-8") as f:
        head = f.read(4096)
        if not head.strip():
            return []
        first = head.lstrip()[:1]
        f.seek(0)

        if first == "[":
            try:
                arr = json.load(f)
            except json.JSONDecodeError as e:
                raise SystemExit(f"{path}: invalid JSON: {e}") from e
            if not isinstance(arr, list):
                raise SystemExit(f"{path}: expected JSON array")
            out: List[Dict[str, Any]] = []
            for i, v in enumerate(arr):
                if not isinstance(v, dict):
                    raise SystemExit(f"{path}: expected array of objects, got {type(v).__name__} at index {i}")
                out.append(v)
            return out

        def it() -> Iterable[Dict[str, Any]]:
            for lineno, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    v = json.loads(line)
                except json.JSONDecodeError as e:
                    raise SystemExit(f"{path}:{lineno}: invalid JSON: {e}") from e
                if not isinstance(v, dict):
                    raise SystemExit(f"{path}:{lineno}: expected object, got {type(v).__name__}")
                yield v

        return it()


def _short_event(ev: str) -> str:
    # Make it less noisy: `exec(TvmLean.Instr.pushInt ...)` -> `exec(pushInt ...)`.
    return (
        ev.replace("TvmLean.Instr.", "")
        .replace("TvmLean.Excno.", "")
        .replace("TvmLean.IntVal.num ", "")
        .replace("TvmLean.IntVal.nan", "NaN")
    )


def _print_tx(r: Dict[str, Any], max_steps: Optional[int], show_all_events: bool) -> None:
    tx = r.get("tx_hash", "<missing tx_hash>")
    status = r.get("status", "<missing status>")
    exp_ec = r.get("expected_exit_code")
    act_ec = r.get("actual_exit_code")
    exp_g = r.get("expected_gas_used")
    act_g = r.get("actual_gas_used")
    err = r.get("error")
    truncated = r.get("trace_truncated") is True

    hdr = f"{tx} {status}"
    if exp_ec is not None or act_ec is not None:
        hdr += f" expected_ec={exp_ec} actual_ec={act_ec}"
    if exp_g is not None or act_g is not None:
        hdr += f" expected_gas={exp_g} actual_gas={act_g}"
    print(hdr)
    if err:
        print(f"  error: {err}")

    trace: List[Dict[str, Any]] = r.get("trace") or []
    if not trace:
        return

    if truncated:
        print("  (trace truncated)")

    shown = 0
    for e in trace:
        if max_steps is not None and shown >= max_steps:
            print("  ...")
            break
        ev = str(e.get("event", ""))
        if not show_all_events and not (
            ev.startswith("exec(")
            or ev.startswith("exec_error(")
            or ev.startswith("decode_error(")
            or ev.startswith("implicit_")
        ):
            continue

        step = e.get("step", "?")
        gas_b = e.get("gas_before")
        gas_a = e.get("gas_after")
        st_b = e.get("stack_before")
        st_a = e.get("stack_after")

        line = f"  {step:>4} {_short_event(ev)}"
        if gas_b is not None and gas_a is not None:
            line += f"  gas {gas_b}->{gas_a}"
        print(line)
        if st_b is not None or st_a is not None:
            print(f"       stack: {st_b} -> {st_a}")
        shown += 1


def main(argv: List[str]) -> int:
    ap = argparse.ArgumentParser(description="Pretty-print tvm-lean diff-test traces from JSONL.")
    ap.add_argument("results", nargs="?", default="diff-test/results-100-trace.jsonl", help="Path to JSONL results")
    ap.add_argument("--tx", action="append", default=[], help="Only show this tx_hash (can repeat)")
    ap.add_argument(
        "--status",
        action="append",
        default=[],
        help="Only show this status (PASS/FAIL/SKIP/ERROR). Can repeat.",
    )
    ap.add_argument("--all", action="store_true", help="Include PASS entries too (default: non-PASS only)")
    ap.add_argument("--max-steps", type=int, default=None, help="Max trace entries to print per tx")
    ap.add_argument("--show-all-events", action="store_true", help="Show all trace events (not just exec/decode/implicit)")
    args = ap.parse_args(argv)

    tx_filter: Set[str] = {t.strip().upper() for t in args.tx if t.strip()}
    status_filter: Set[str] = {s.strip().upper() for s in args.status if s.strip()}

    first = True
    for r in _load_results(args.results):
        st = str(r.get("status", "")).upper()
        if not args.all and not status_filter and st == "PASS":
            continue
        if status_filter and st not in status_filter:
            continue
        tx = str(r.get("tx_hash", "")).upper()
        if tx_filter and tx not in tx_filter:
            continue

        if not first:
            print()
        first = False
        _print_tx(r, max_steps=args.max_steps, show_all_events=args.show_all_events)

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
