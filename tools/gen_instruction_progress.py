#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SPEC_INDEX_JSON = REPO_ROOT / "docs/progress/tvm_spec_index.json"
LEGACY_PROGRESS_CSV = REPO_ROOT / "docs/progress/instructions.csv"
OUT_CSV = REPO_ROOT / "docs/progress/instructions_full.csv"

# Prefer Linear as the source of truth when available (per docs/linear-backlog.md).
LINEAR_GRAPHQL_URL = "https://api.linear.app/graphql"

# NOTE: These IDs are workspace-specific. Keep in sync with `tools/linear_sync.py`.
LINEAR_TEAM_ID = "5c9dcc9f-5d33-4a9e-8fc2-b568b75a1edd"  # TVM Formal Verification
LINEAR_PROJECT_ID = "ee1015c4-d885-4426-9277-da0bb9bdf53e"  # Instruction Coverage (TVM Spec)

SPEC_KEY_RE = re.compile(r"(?m)^[ \t]*SpecKey:[ \t]*([^\s]+)[ \t]*$")
SUB_KEY_RE = re.compile(r"(?m)^[ \t]*SubKey:[ \t]*([^\s]+)[ \t]*$")


class LinearHttpError(RuntimeError):
    def __init__(self, code: int, body: str):
        super().__init__(f"HTTP {code}: {body[:500]}")
        self.code = code
        self.body = body


def _load_dotenv(path: Path) -> None:
    # Minimal `.env` loader (avoid extra dependencies). Only sets vars that are not already set.
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return

    for line in raw.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith("export "):
            s = s[len("export ") :].strip()
        if "=" not in s:
            continue
        key, value = s.split("=", 1)
        key = key.strip()
        if not key or key in os.environ:
            continue
        value = value.strip()
        if not value:
            continue
        if value[0] in ("'", '"') and len(value) >= 2 and value[-1] == value[0]:
            value = value[1:-1]
        else:
            # Strip inline comments for unquoted values.
            value = value.split("#", 1)[0].strip()
        if value:
            os.environ[key] = value


def _maybe_retry(fn, *, max_tries: int = 6, base_sleep_s: float = 0.5):
    retryable_http = {408, 429, 500, 502, 503, 504}
    last_err: Exception | None = None
    for i in range(max_tries):
        try:
            return fn()
        except LinearHttpError as e:
            # Linear: retry on transient failures and rate limiting.
            if e.code in {401}:
                raise
            if e.code in retryable_http or ("rate limit" in (e.body or "").lower()):
                last_err = e
            else:
                raise
        except Exception as e:
            last_err = e
        time.sleep(base_sleep_s * (2**i))
    assert last_err is not None
    raise last_err


def _linear_graphql(token: str, query: str, variables: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = {"query": query, "variables": variables or {}}
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        LINEAR_GRAPHQL_URL,
        data=body,
        headers={"Content-Type": "application/json", "Authorization": token},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = json.load(resp)
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8", errors="replace")
        raise LinearHttpError(e.code, msg) from e
    except Exception as e:
        raise RuntimeError(f"Linear API request failed: {e}") from e

    if "errors" in data:
        raise RuntimeError(f"Linear API GraphQL errors: {data['errors']}")
    out = data.get("data") or {}
    if not isinstance(out, dict):
        return {}
    return out


def _extract_spec_key(description: str | None) -> str | None:
    if not description:
        return None
    m = SPEC_KEY_RE.search(description)
    return m.group(1) if m else None


def _extract_sub_key(description: str | None) -> str | None:
    if not description:
        return None
    m = SUB_KEY_RE.search(description)
    return m.group(1) if m else None


def _load_linear_progress(*, token: str) -> dict[str, tuple[bool, bool]]:
    """
    Return a map: spec_key (e.g. "tvm::ADD") -> (implemented, tested).

    Rules:
    - implemented := ws/impl subissue is in a completed state.
    - tested := ws/tests subissue is in a completed state.
    - Fallback: if there are no ws/* subissues, mark implemented/tested from the parent issue state.
      (This supports older/manual cases.)
    """
    query = """
    query Issues($teamId: ID!, $projectId: ID!, $after: String) {
      issues(
        first: 250,
        after: $after,
        filter: { team: { id: { eq: $teamId } }, project: { id: { eq: $projectId } } }
      ) {
        pageInfo { hasNextPage endCursor }
        nodes {
          id
          description
          state { type name }
        }
      }
    }
    """

    parent_state_type: dict[str, str] = {}
    sub_state_type: dict[tuple[str, str], str] = {}  # (spec_key, ws) -> state.type

    after: str | None = None
    while True:
        vars: dict[str, Any] = {"teamId": LINEAR_TEAM_ID, "projectId": LINEAR_PROJECT_ID, "after": after}
        data = _maybe_retry(lambda: _linear_graphql(token, query, vars))
        issues = (data.get("issues", {}) or {}).get("nodes", []) or []
        for node in issues:
            if not isinstance(node, dict):
                continue
            desc = node.get("description")
            state = node.get("state") or {}
            state_type = str(state.get("type") or "").strip()

            spec_key = _extract_spec_key(desc)
            if spec_key:
                parent_state_type[spec_key] = state_type
                continue

            sub_key = _extract_sub_key(desc)
            if not sub_key:
                continue
            # SubKey: <spec_key>::<ws_label>
            if "::" not in sub_key:
                continue
            parent_key, ws = sub_key.rsplit("::", 1)
            sub_state_type[(parent_key, ws)] = state_type

        page_info = (data.get("issues", {}) or {}).get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        after = page_info.get("endCursor")
        if not after:
            break

    out: dict[str, tuple[bool, bool]] = {}

    # Prefer ws/* status when present; fallback to parent.
    all_parent_keys = set(parent_state_type.keys()) | {k for (k, _ws) in sub_state_type.keys()}
    for spec_key in all_parent_keys:
        impl_state = sub_state_type.get((spec_key, "ws/impl"), "")
        tests_state = sub_state_type.get((spec_key, "ws/tests"), "")
        if impl_state or tests_state:
            out[spec_key] = (impl_state == "completed", tests_state == "completed")
        else:
            st = parent_state_type.get(spec_key, "")
            is_done = st == "completed"
            out[spec_key] = (is_done, False)

    return out


def _load_json(path: Path) -> Any:
    with path.open("rb") as f:
        return json.load(f)


def _load_legacy_progress(path: Path) -> dict[str, tuple[bool, bool]]:
    if not path.exists():
        return {}
    out: dict[str, tuple[bool, bool]] = {}
    with path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        # legacy format: instruction,implemented,tested
        for row in r:
            name = (row.get("instruction") or "").strip()
            if not name:
                continue
            impl = (row.get("implemented") or "").strip().lower() == "true"
            tested = (row.get("tested") or "").strip().lower() == "true"
            out[name] = (impl, tested)
    return out


def _count_progress(progress: dict[str, tuple[bool, bool]]) -> tuple[int, int]:
    implemented = sum(1 for (impl, _t) in progress.values() if impl)
    tested = sum(1 for (_i, tested) in progress.values() if tested)
    return implemented, tested


def _load_code_progress() -> dict[str, tuple[bool, bool]]:
    """
    Probe the actual Lean decoder/exec to determine which spec opcodes are implemented.

    An opcode counts as implemented if:
    - it decodes via `decodeCp0WithBits`, and
    - executing the decoded `Instr` does not raise `invOpcode` (other runtime errors are treated as implemented).

    This currently does not infer `tested` and returns it as `False`.
    """
    cmd = ["lake", "exe", "tvm-lean-progress", "--", "--tsv"]
    p = subprocess.run(cmd, cwd=REPO_ROOT, check=False, capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(
            "failed to run code progress probe:\n"
            + f"cmd: {' '.join(cmd)}\n"
            + (p.stdout or "")
            + (p.stderr or "")
        )
    out: dict[str, tuple[bool, bool]] = {}
    for line in (p.stdout or "").splitlines():
        s = line.strip()
        if not s:
            continue
        if "\t" not in s:
            continue
        k, v = s.split("\t", 1)
        out[k.strip()] = (v.strip().lower() == "true", False)
    return out


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Generate docs/progress/instructions_full.csv.\n\n"
            "By default, uses Linear (LINEAR_API_KEY from .env or env) when available, otherwise falls back to the "
            "legacy docs/progress/instructions.csv seed."
        )
    )
    parser.add_argument(
        "--source",
        choices=["auto", "linear", "legacy", "code"],
        default="auto",
        help="Progress source: auto (default), linear, legacy, or code (probe Lean decoder/exec).",
    )
    parser.add_argument(
        "--linear-token",
        default="",
        help="Optional Linear API key override (otherwise uses LINEAR_API_KEY from env/.env).",
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print summary counts to stdout (implemented/tested), split by tvm/fift.",
    )

    args = parser.parse_args(argv)

    if not SPEC_INDEX_JSON.exists():
        raise SystemExit(f"missing {SPEC_INDEX_JSON}; run tools/gen_spec_index.py first")

    idx = _load_json(SPEC_INDEX_JSON)
    tvm: list[dict[str, Any]] = idx["tvm_instructions"]
    fift: list[dict[str, Any]] = idx["fift_instructions"]

    _load_dotenv(REPO_ROOT / ".env")

    legacy = _load_legacy_progress(LEGACY_PROGRESS_CSV)
    linear_token = (args.linear_token or os.environ.get("LINEAR_API_KEY") or "").strip()

    use_linear = False
    linear_progress: dict[str, tuple[bool, bool]] = {}
    code_progress: dict[str, tuple[bool, bool]] = {}

    if args.source == "code":
        code_progress = _load_code_progress()
    else:
        if args.source == "linear":
            if not linear_token:
                raise SystemExit("missing Linear API key (set LINEAR_API_KEY or pass --linear-token)")
            use_linear = True
        elif args.source == "auto":
            use_linear = bool(linear_token)

        if use_linear:
            linear_progress = _load_linear_progress(token=linear_token)

    OUT_CSV.parent.mkdir(parents=True, exist_ok=True)
    with OUT_CSV.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["kind", "name", "category", "sub_category", "implemented", "tested", "notes"])

        for ins in tvm:
            name = ins["name"]
            if args.source == "code":
                impl, tested = code_progress.get(f"tvm::{name}", (False, False))
            elif use_linear:
                impl, tested = linear_progress.get(f"tvm::{name}", (False, False))
            else:
                impl, tested = legacy.get(name, (False, False))
            w.writerow(["tvm", name, ins.get("category", ""), ins.get("sub_category", ""), str(impl).lower(), str(tested).lower(), ""])

        for fa in fift:
            name = fa["name"]
            impl, tested = (False, False)
            if use_linear:
                impl, tested = linear_progress.get(f"fift::{name}", (False, False))
            w.writerow(
                [
                    "fift",
                    name,
                    fa.get("actual_category") or "",
                    fa.get("actual_sub_category") or "",
                    str(impl).lower(),
                    str(tested).lower(),
                    f"alias of {fa['actual_name']}",
                ]
            )

    print(f"wrote {OUT_CSV}")
    if args.summary:
        tvm_prog = {f"tvm::{ins['name']}": (False, False) for ins in tvm}
        fift_prog = {f"fift::{fa['name']}": (False, False) for fa in fift}
        if args.source == "code":
            src = code_progress
        else:
            src = linear_progress if use_linear else {**{f"tvm::{k}": v for k, v in legacy.items()}}
        for k in list(tvm_prog.keys()):
            if k in src:
                tvm_prog[k] = src[k]
        for k in list(fift_prog.keys()):
            if k in src:
                fift_prog[k] = src[k]

        tvm_impl, tvm_tested = _count_progress(tvm_prog)
        fift_impl, fift_tested = _count_progress(fift_prog)
        print(
            f"tvm: implemented={tvm_impl}/{len(tvm)} tested={tvm_tested}/{len(tvm)} | "
            f"fift: implemented={fift_impl}/{len(fift)} tested={fift_tested}/{len(fift)}"
        )


if __name__ == "__main__":
    main()
