#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import sqlite3
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]

TASKS_LIST_URL = "https://chatgpt.com/backend-api/wham/tasks/list"
PR_URL_TEMPLATE = "https://chatgpt.com/backend-api/wham/tasks/{task_id}/turns/{turn_id}/pr"

MAX_TASKS_LIST_LIMIT = 19  # server rejects higher with 400
DEFAULT_TASK_FILTER = "current"  # allowed: all, current, archived, code_review
DEFAULT_ENV_LABEL_SUBSTR = "tvm-lean"


class HttpError(RuntimeError):
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


def _http_json(
    token: str,
    url: str,
    *,
    method: str = "GET",
    params: dict[str, Any] | None = None,
    body: Any | None = None,
    headers: dict[str, str] | None = None,
    timeout_s: float = 30.0,
) -> Any:
    if params:
        qs = urllib.parse.urlencode({k: v for k, v in params.items() if v is not None})
        url = f"{url}?{qs}"

    req_headers: dict[str, str] = {
        "Accept": "application/json",
        "Authorization": f"Bearer {token}",
        "OAI-Language": "en-US",
    }
    if body is not None:
        req_headers["Content-Type"] = "application/json"

    if headers:
        req_headers.update(headers)

    data: bytes | None = None
    if body is not None:
        data = json.dumps(body).encode("utf-8")

    req = urllib.request.Request(url, data=data, headers=req_headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as e:
        raw = e.read().decode("utf-8", errors="replace")
        raise HttpError(e.code, raw) from e
    except Exception as e:
        raise RuntimeError(f"request failed: {e}") from e

    try:
        return json.loads(raw) if raw else None
    except Exception as e:
        raise RuntimeError(f"non-JSON response: {raw[:200]}") from e


def _maybe_retry(fn, *, max_tries: int = 6, base_sleep_s: float = 0.5):
    retryable_http = {429, 500, 502, 503, 504}
    last_err: Exception | None = None
    for i in range(max_tries):
        try:
            return fn()
        except HttpError as e:
            if e.code in {401, 403}:
                raise
            if e.code not in retryable_http:
                raise
            last_err = e
        except Exception as e:
            last_err = e
        time.sleep(base_sleep_s * (2**i))
    assert last_err is not None
    raise last_err


@dataclass(frozen=True)
class TaskRef:
    task_id: str
    title: str
    updated_at: float
    env_label: str
    turn_id: str
    turn_status: str
    pull_request_count: int


def _extract_task_ref(item: dict[str, Any]) -> TaskRef | None:
    task_id = item.get("id")
    if not isinstance(task_id, str) or not task_id:
        return None

    title = item.get("title") or ""
    updated_at = item.get("updated_at")
    if not isinstance(updated_at, (int, float)):
        updated_at = 0.0

    tsd = item.get("task_status_display") or {}
    if not isinstance(tsd, dict):
        tsd = {}
    env_label = tsd.get("environment_label") or ""
    if not isinstance(env_label, str):
        env_label = ""

    ltd = tsd.get("latest_turn_status_display") or {}
    if not isinstance(ltd, dict):
        ltd = {}
    turn_id = ltd.get("turn_id") or ""
    turn_status = ltd.get("turn_status") or ""
    if not isinstance(turn_id, str) or not isinstance(turn_status, str):
        return None

    prs = item.get("pull_requests") or []
    pr_count = len(prs) if isinstance(prs, list) else 0

    return TaskRef(
        task_id=task_id,
        title=str(title),
        updated_at=float(updated_at),
        env_label=env_label,
        turn_id=turn_id,
        turn_status=turn_status,
        pull_request_count=pr_count,
    )


def _db_connect(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS pr_requests (
          turn_id TEXT PRIMARY KEY,
          task_id TEXT NOT NULL,
          created_at REAL NOT NULL,
          status TEXT NOT NULL,
          http_status INTEGER,
          message TEXT
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_pr_requests_task ON pr_requests(task_id)")
    return conn


def _db_get(conn: sqlite3.Connection, turn_id: str) -> tuple[str, float] | None:
    row = conn.execute("SELECT status, created_at FROM pr_requests WHERE turn_id = ?", (turn_id,)).fetchone()
    if not row:
        return None
    status, created_at = row
    return str(status), float(created_at)


def _db_put(
    conn: sqlite3.Connection,
    *,
    turn_id: str,
    task_id: str,
    status: str,
    http_status: int | None = None,
    message: str | None = None,
) -> None:
    conn.execute(
        """
        INSERT INTO pr_requests(turn_id, task_id, created_at, status, http_status, message)
        VALUES(?, ?, ?, ?, ?, ?)
        ON CONFLICT(turn_id) DO UPDATE SET
          task_id=excluded.task_id,
          status=excluded.status,
          http_status=excluded.http_status,
          message=excluded.message
        """,
        (turn_id, task_id, time.time(), status, http_status, message),
    )
    conn.commit()


def _fetch_tasks_page(
    token: str,
    *,
    task_filter: str,
    limit: int,
    cursor: str | None,
) -> tuple[list[dict[str, Any]], str | None]:
    params: dict[str, Any] = {"limit": limit, "task_filter": task_filter}
    if cursor:
        params["cursor"] = cursor

    data = _maybe_retry(lambda: _http_json(token, TASKS_LIST_URL, params=params))
    if not isinstance(data, dict):
        raise RuntimeError(f"unexpected tasks/list response type: {type(data).__name__}")
    items = data.get("items") or []
    if not isinstance(items, list):
        raise RuntimeError("unexpected tasks/list response: items is not a list")
    next_cursor = data.get("cursor")
    if next_cursor is not None and not isinstance(next_cursor, str):
        next_cursor = None
    return [it for it in items if isinstance(it, dict)], next_cursor


def _request_pr(token: str, *, task_id: str, turn_id: str) -> Any:
    url = PR_URL_TEMPLATE.format(task_id=task_id, turn_id=turn_id)
    headers = {"Referer": f"https://chatgpt.com/codex/tasks/{task_id}"}
    return _maybe_retry(lambda: _http_json(token, url, method="POST", body={}, headers=headers, timeout_s=60.0))


def _is_tvm_lean_task(env_label: str, *, env_label_substr: str) -> bool:
    if not env_label_substr:
        return True
    return env_label_substr.lower() in env_label.lower()


def run_once(
    *,
    conn: sqlite3.Connection,
    token: str,
    env_label_substr: str,
    task_filter: str,
    limit: int,
    lookback_hours: float,
    max_pages: int,
    min_seconds_between_pr: float,
    retry_cooldown_s: float,
    dry_run: bool,
    verbose: bool,
) -> int:
    now = time.time()
    cutoff = now - lookback_hours * 3600.0 if lookback_hours > 0 else None

    scanned = 0
    tvm_lean = 0
    ready = 0
    pr_requested = 0
    skipped_existing_pr = 0
    skipped_attempted = 0
    skipped_old = 0

    cursor: str | None = None
    for page in range(max_pages):
        items, cursor = _fetch_tasks_page(token, task_filter=task_filter, limit=limit, cursor=cursor)
        if not items:
            break

        scanned += len(items)

        # Stop early if we're beyond the lookback window (tasks list is sorted by updated_at desc).
        if cutoff is not None:
            oldest = items[-1].get("updated_at")
            if isinstance(oldest, (int, float)) and float(oldest) < cutoff:
                # Still process this page; later pages will be older.
                stop_after_page = True
            else:
                stop_after_page = False
        else:
            stop_after_page = False

        for item in items:
            if item.get("archived") is True:
                continue

            ref = _extract_task_ref(item)
            if not ref:
                continue

            if not _is_tvm_lean_task(ref.env_label, env_label_substr=env_label_substr):
                continue

            tvm_lean += 1

            if cutoff is not None and ref.updated_at and ref.updated_at < cutoff:
                skipped_old += 1
                continue

            if ref.pull_request_count > 0:
                skipped_existing_pr += 1
                continue

            if ref.turn_status != "completed":
                continue

            ready += 1

            prev = _db_get(conn, ref.turn_id)
            if prev:
                prev_status, prev_at = prev
                # Skip successful requests forever; throttle retries for failures.
                if prev_status == "requested":
                    skipped_attempted += 1
                    continue
                if now - prev_at < retry_cooldown_s:
                    skipped_attempted += 1
                    continue

            if dry_run:
                if verbose:
                    print(f"[dry-run] would create PR: {ref.task_id} turn={ref.turn_id} title={ref.title}")
                continue

            if verbose:
                print(f"creating PR: {ref.task_id} turn={ref.turn_id} title={ref.title}")

            try:
                resp = _request_pr(token, task_id=ref.task_id, turn_id=ref.turn_id)
                ok = True
                if isinstance(resp, dict) and "success" in resp:
                    ok = bool(resp.get("success"))
                if ok:
                    _db_put(conn, turn_id=ref.turn_id, task_id=ref.task_id, status="requested", http_status=200)
                    pr_requested += 1
                else:
                    _db_put(
                        conn,
                        turn_id=ref.turn_id,
                        task_id=ref.task_id,
                        status="failed",
                        http_status=200,
                        message=str(resp)[:500],
                    )
                    if verbose:
                        print(f"  WARN: /pr returned success=false for {ref.task_id}: {resp}")
            except HttpError as e:
                if e.code in {401, 403}:
                    print("ERROR: CODEX_TOKEN rejected (401/403). Refresh token and retry.", file=sys.stderr)
                    raise
                _db_put(
                    conn,
                    turn_id=ref.turn_id,
                    task_id=ref.task_id,
                    status="failed",
                    http_status=e.code,
                    message=e.body[:500],
                )
                if verbose:
                    print(f"  ERROR: /pr failed for {ref.task_id}: HTTP {e.code}")
            except Exception as e:
                _db_put(conn, turn_id=ref.turn_id, task_id=ref.task_id, status="error", message=str(e)[:500])
                if verbose:
                    print(f"  ERROR: /pr error for {ref.task_id}: {e}")

            if min_seconds_between_pr > 0:
                time.sleep(min_seconds_between_pr)

        if stop_after_page or cursor is None:
            break

    print(
        "autopr:",
        f"scanned={scanned}",
        f"tvm_lean={tvm_lean}",
        f"ready={ready}",
        f"requested={pr_requested}",
        f"skipped_existing_pr={skipped_existing_pr}",
        f"skipped_attempted={skipped_attempted}",
        f"skipped_old={skipped_old}",
        flush=True,
    )
    return 0


def main() -> int:
    _load_dotenv(REPO_ROOT / ".env")

    parser = argparse.ArgumentParser(
        description=(
            "Auto-create GitHub PRs for completed Codex tasks.\n\n"
            "This polls the Codex tasks list, finds completed tasks for this repo that don't yet have a PR, "
            "and calls the internal /pr endpoint. State is persisted locally to avoid duplicates."
        )
    )
    parser.add_argument(
        "--token",
        default=os.getenv("CODEX_TOKEN") or "",
        help="ChatGPT/Codex bearer token (or set CODEX_TOKEN).",
    )
    parser.add_argument(
        "--state",
        default=str(REPO_ROOT / ".autopr" / "state.sqlite3"),
        help="Path to sqlite state DB (default: .autopr/state.sqlite3).",
    )
    parser.add_argument(
        "--env-label-substr",
        default=DEFAULT_ENV_LABEL_SUBSTR,
        help="Only handle tasks whose environment_label contains this substring (case-insensitive).",
    )
    parser.add_argument(
        "--task-filter",
        default=DEFAULT_TASK_FILTER,
        help="tasks/list filter: all|current|archived|code_review (default: current).",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=MAX_TASKS_LIST_LIMIT,
        help=f"tasks/list page size (max {MAX_TASKS_LIST_LIMIT}).",
    )
    parser.add_argument(
        "--lookback-hours",
        type=float,
        default=24 * 14,
        help="Only consider tasks updated within this many hours (0 = no limit).",
    )
    parser.add_argument(
        "--max-pages",
        type=int,
        default=200,
        help="Maximum pages to scan per run (safety cap).",
    )
    parser.add_argument(
        "--min-seconds-between-pr",
        type=float,
        default=0.5,
        help="Sleep between /pr requests to reduce rate-limit risk.",
    )
    parser.add_argument(
        "--retry-cooldown-seconds",
        type=float,
        default=10 * 60,
        help="Minimum seconds before retrying a previously failed turn_id.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Don't create PRs; just print what would happen.")
    parser.add_argument("--verbose", action="store_true", help="Verbose logs.")

    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--once", action="store_true", help="Run one scan and exit (default).")
    mode.add_argument("--watch", action="store_true", help="Run forever, polling periodically.")
    parser.set_defaults(once=True)
    parser.add_argument(
        "--interval-seconds",
        type=float,
        default=60.0,
        help="Polling interval for --watch.",
    )

    args = parser.parse_args()

    token = args.token.strip()
    if not token:
        print("Missing CODEX_TOKEN. Provide --token or set CODEX_TOKEN in .env.", file=sys.stderr)
        return 2

    if args.task_filter not in {"all", "current", "archived", "code_review"}:
        print("Invalid --task-filter. Expected one of: all, current, archived, code_review.", file=sys.stderr)
        return 2

    if args.limit < 1 or args.limit > MAX_TASKS_LIST_LIMIT:
        print(f"Invalid --limit. Must be between 1 and {MAX_TASKS_LIST_LIMIT}.", file=sys.stderr)
        return 2

    conn = _db_connect(Path(args.state))

    while True:
        try:
            run_once(
                conn=conn,
                token=token,
                env_label_substr=args.env_label_substr,
                task_filter=args.task_filter,
                limit=args.limit,
                lookback_hours=args.lookback_hours,
                max_pages=args.max_pages,
                min_seconds_between_pr=args.min_seconds_between_pr,
                retry_cooldown_s=args.retry_cooldown_seconds,
                dry_run=bool(args.dry_run),
                verbose=bool(args.verbose),
            )
        except HttpError as e:
            if e.code in {401, 403}:
                return 3
            print(f"ERROR: {e}", file=sys.stderr)
        except Exception as e:
            print(f"ERROR: {e}", file=sys.stderr)

        if args.watch:
            time.sleep(max(1.0, float(args.interval_seconds)))
            continue
        return 0


if __name__ == "__main__":
    raise SystemExit(main())

