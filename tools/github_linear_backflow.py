#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sqlite3
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]

GITHUB_API = "https://api.github.com"
LINEAR_GRAPHQL = "https://api.linear.app/graphql"

DEFAULT_TARGET_BRANCH = "main"
DEFAULT_HEAD_BRANCH_PREFIX = "codex/"
DEFAULT_LOOKBACK_HOURS = 24 * 14
DEFAULT_TODO_STATE_NAME = "Todo"
DEFAULT_CODEX_NAME_SUBSTR = "codex"
DEFAULT_TEAM_KEY = "TVM"

LINEAR_TEAM_ID = "5c9dcc9f-5d33-4a9e-8fc2-b568b75a1edd"  # TVM Formal Verification

LINEAR_ID_RE = re.compile(r"\b([A-Za-z][A-Za-z0-9]+)-(\d+)\b")


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


def _maybe_retry(fn, *, max_tries: int = 6, base_sleep_s: float = 0.5):
    retryable_http = {408, 429, 500, 502, 503, 504}
    last_err: Exception | None = None
    for i in range(max_tries):
        try:
            return fn()
        except HttpError as e:
            body_lower = e.body.lower()
            if e.code in {401}:
                raise
            if e.code in {403} and "rate limit" in body_lower:
                last_err = e
            elif e.code in retryable_http:
                last_err = e
            else:
                raise
        except Exception as e:
            last_err = e
        time.sleep(base_sleep_s * (2**i))
    assert last_err is not None
    raise last_err


def _detect_owner_repo() -> tuple[str, str]:
    # Prefer env (works in CI / custom setups).
    env_repo = (
        os.environ.get("GITHUB_REPOSITORY")
        or os.environ.get("GH_REPO")
        or os.environ.get("GITHUB_REPO")
        or os.environ.get("GITHUB_REPO_SLUG")
    )
    if env_repo:
        parts = env_repo.strip().split("/")
        if len(parts) >= 2:
            owner, repo = parts[-2], parts[-1]
            if owner and repo:
                return owner, repo.removesuffix(".git")

    # Fallback: parse git remote URL.
    try:
        remote = (
            subprocess.check_output(["git", "config", "--get", "remote.origin.url"], cwd=REPO_ROOT, text=True)
            .strip()
            .rstrip("/")
        )
    except Exception:
        raise RuntimeError("failed to detect GitHub repo; set GITHUB_REPOSITORY=owner/repo")

    if remote.startswith("git@"):
        _, path = remote.split(":", 1) if ":" in remote else ("", "")
        owner, repo = path.split("/", 1)
        return owner, repo.removesuffix(".git")

    if remote.startswith("https://") or remote.startswith("http://"):
        u = urllib.parse.urlparse(remote)
        path = (u.path or "").lstrip("/")
        owner, repo = path.split("/", 1)
        return owner, repo.removesuffix(".git")

    raise RuntimeError(f"unsupported remote.origin.url format: {remote}")


def _github_http_json(
    token: str,
    url: str,
    *,
    method: str = "GET",
    params: dict[str, Any] | None = None,
    timeout_s: float = 30.0,
) -> Any:
    if params:
        qs = urllib.parse.urlencode({k: v for k, v in params.items() if v is not None})
        url = f"{url}?{qs}"

    req = urllib.request.Request(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
        method=method,
    )
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


def _linear_graphql(token: str, query: str, variables: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = {"query": query, "variables": variables or {}}
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        LINEAR_GRAPHQL,
        data=body,
        headers={"Content-Type": "application/json", "Authorization": token},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = json.load(resp)
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Linear API HTTP error: {e.code} {e.reason}: {msg}") from e
    except Exception as e:
        raise RuntimeError(f"Linear API request failed: {e}") from e

    if "errors" in data:
        raise RuntimeError(f"Linear API GraphQL errors: {data['errors']}")
    out = data.get("data") or {}
    if not isinstance(out, dict):
        return {}
    return out


def _parse_github_time(ts: str) -> float:
    # Example: "2026-02-01T12:34:56Z"
    dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
    return dt.timestamp()


def _extract_linear_ids(*texts: str) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for t in texts:
        for m in LINEAR_ID_RE.finditer(t or ""):
            key, num = m.group(1), m.group(2)
            ident = f"{key.upper()}-{int(num)}"
            if ident not in seen:
                seen.add(ident)
                out.append(ident)
    return out


def _pick_linear_id(cands: list[str], *, prefer_team_key: str) -> str | None:
    if not cands:
        return None
    prefer = prefer_team_key.strip().upper()
    if prefer:
        preferred = [c for c in cands if c.startswith(prefer + "-")]
        if preferred:
            return preferred[0]
    return cands[0]


@dataclass(frozen=True)
class ClosedPr:
    number: int
    title: str
    html_url: str
    head_ref: str
    merged_at: str | None
    updated_at: str


def _list_closed_prs(
    token: str,
    *,
    owner: str,
    repo: str,
    base_branch: str,
    head_branch_prefix: str,
    lookback_hours: float,
    max_prs: int,
) -> list[ClosedPr]:
    cutoff = time.time() - lookback_hours * 3600.0 if lookback_hours > 0 else None
    out: list[ClosedPr] = []

    per_page = 100
    page = 1
    while len(out) < max_prs:
        data = _maybe_retry(
            lambda: _github_http_json(
                token,
                f"{GITHUB_API}/repos/{owner}/{repo}/pulls",
                params={
                    "state": "closed",
                    "base": base_branch,
                    "sort": "updated",
                    "direction": "desc",
                    "per_page": per_page,
                    "page": page,
                },
            )
        )
        if not isinstance(data, list) or not data:
            break

        for pr in data:
            if not isinstance(pr, dict):
                continue

            try:
                number = int(pr["number"])
                title = str(pr.get("title") or "")
                html_url = str(pr.get("html_url") or "")
                head_ref = str(((pr.get("head") or {}) if isinstance(pr.get("head"), dict) else {}).get("ref") or "")
                merged_at = pr.get("merged_at")
                merged_at = str(merged_at) if isinstance(merged_at, str) else None
                updated_at = str(pr.get("updated_at") or "")
            except Exception:
                continue

            if head_branch_prefix and not head_ref.startswith(head_branch_prefix):
                continue

            if cutoff is not None and updated_at:
                try:
                    if _parse_github_time(updated_at) < cutoff:
                        return out
                except Exception:
                    pass

            out.append(
                ClosedPr(
                    number=number,
                    title=title,
                    html_url=html_url,
                    head_ref=head_ref,
                    merged_at=merged_at,
                    updated_at=updated_at,
                )
            )
            if len(out) >= max_prs:
                break

        page += 1

    return out


def _issue_state_reason(token: str, *, owner: str, repo: str, issue_number: int) -> tuple[str, str | None, str]:
    data = _maybe_retry(
        lambda: _github_http_json(token, f"{GITHUB_API}/repos/{owner}/{repo}/issues/{issue_number}")
    )
    if not isinstance(data, dict):
        raise RuntimeError(f"unexpected issue response type: {type(data).__name__}")
    state = str(data.get("state") or "")
    state_reason_raw = data.get("state_reason")
    state_reason = str(state_reason_raw) if isinstance(state_reason_raw, str) else None
    updated_at = str(data.get("updated_at") or "")
    return state, state_reason, updated_at


def _db_connect(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS pr_backflow (
          pr_number INTEGER PRIMARY KEY,
          pr_updated_at TEXT NOT NULL,
          status TEXT NOT NULL,
          linear_id TEXT,
          message TEXT,
          processed_at REAL NOT NULL
        )
        """
    )
    return conn


def _db_get(conn: sqlite3.Connection, pr_number: int) -> tuple[str, str] | None:
    row = conn.execute("SELECT pr_updated_at, status FROM pr_backflow WHERE pr_number = ?", (pr_number,)).fetchone()
    if not row:
        return None
    pr_updated_at, status = row
    return str(pr_updated_at), str(status)


def _db_put(
    conn: sqlite3.Connection,
    *,
    pr_number: int,
    pr_updated_at: str,
    status: str,
    linear_id: str | None = None,
    message: str | None = None,
) -> None:
    conn.execute(
        """
        INSERT INTO pr_backflow(pr_number, pr_updated_at, status, linear_id, message, processed_at)
        VALUES(?, ?, ?, ?, ?, ?)
        ON CONFLICT(pr_number) DO UPDATE SET
          pr_updated_at=excluded.pr_updated_at,
          status=excluded.status,
          linear_id=excluded.linear_id,
          message=excluded.message,
          processed_at=excluded.processed_at
        """,
        (pr_number, pr_updated_at, status, linear_id, message, time.time()),
    )
    conn.commit()


@dataclass(frozen=True)
class LinearIssueRef:
    id: str
    identifier: str
    state_id: str
    state_name: str
    assignee_id: str | None
    assignee_name: str | None
    delegate_id: str | None
    delegate_name: str | None


def _linear_fetch_issue(token: str, *, identifier: str) -> LinearIssueRef | None:
    query_with_delegate = """
    query Issue($id: String!) {
      issue(id: $id) {
        id
        identifier
        state { id name }
        assignee { id name }
        delegate { id name }
      }
    }
    """

    query_without_delegate = """
    query Issue($id: String!) {
      issue(id: $id) {
        id
        identifier
        state { id name }
        assignee { id name }
      }
    }
    """

    try:
        data = _maybe_retry(lambda: _linear_graphql(token, query_with_delegate, {"id": identifier}))
    except Exception as e:
        # Older Linear workspaces may not have the delegate field.
        if "delegate" in str(e) and "Cannot query field" in str(e):
            data = _maybe_retry(lambda: _linear_graphql(token, query_without_delegate, {"id": identifier}))
        else:
            raise
    node = (data.get("issue") or {}) if isinstance(data, dict) else {}
    if not isinstance(node, dict) or not node.get("id"):
        return None
    state = node.get("state") or {}
    assignee = node.get("assignee") or {}
    delegate = node.get("delegate") or {}
    return LinearIssueRef(
        id=str(node["id"]),
        identifier=str(node.get("identifier") or identifier),
        state_id=str((state.get("id") or "")),
        state_name=str((state.get("name") or "")),
        assignee_id=str(assignee.get("id")) if isinstance(assignee, dict) and assignee.get("id") else None,
        assignee_name=str(assignee.get("name")) if isinstance(assignee, dict) and assignee.get("name") else None,
        delegate_id=str(delegate.get("id")) if isinstance(delegate, dict) and delegate.get("id") else None,
        delegate_name=str(delegate.get("name")) if isinstance(delegate, dict) and delegate.get("name") else None,
    )


def _linear_find_state_id(token: str, *, team_id: str, state_name: str) -> str:
    query_workflow_states = """
    query States($teamId: ID!) {
      workflowStates(first: 100, filter: { team: { id: { eq: $teamId } } }) {
        nodes { id name }
      }
    }
    """
    query_team_states = """
    query TeamStates($teamId: String!) {
      team(id: $teamId) {
        states(first: 100) { nodes { id name } }
      }
    }
    """

    try:
        data = _maybe_retry(lambda: _linear_graphql(token, query_workflow_states, {"teamId": team_id}))
        nodes = ((data.get("workflowStates") or {}).get("nodes") or []) if isinstance(data, dict) else []
    except Exception as e:
        # Fallback for schema variants.
        if "workflowStates" in str(e) and "Cannot query field" in str(e):
            data = _maybe_retry(lambda: _linear_graphql(token, query_team_states, {"teamId": team_id}))
            nodes = (((data.get("team") or {}).get("states") or {}).get("nodes") or []) if isinstance(data, dict) else []
        else:
            raise
    if not isinstance(nodes, list):
        nodes = []
    want = state_name.strip().lower()
    for n in nodes:
        if not isinstance(n, dict):
            continue
        name = str(n.get("name") or "")
        if name.strip().lower() == want and n.get("id"):
            return str(n["id"])
    raise RuntimeError(f"failed to find Linear workflow state named {state_name!r} for team {team_id}")


def _linear_issue_update(token: str, *, issue_id: str, input_obj: dict[str, Any]) -> None:
    mutation = """
    mutation IssueUpdate($id: String!, $input: IssueUpdateInput!) {
      issueUpdate(id: $id, input: $input) {
        success
        issue { id }
      }
    }
    """
    _maybe_retry(lambda: _linear_graphql(token, mutation, {"id": issue_id, "input": input_obj}))


def run_once(
    *,
    conn: sqlite3.Connection,
    github_token: str,
    linear_token: str,
    linear_team_id: str,
    base_branch: str,
    head_branch_prefix: str,
    lookback_hours: float,
    max_prs: int,
    todo_state_name: str,
    prefer_team_key: str,
    codex_name_substr: str,
    clear_assignee: bool,
    clear_delegate: bool,
    dry_run: bool,
    verbose: bool,
) -> int:
    owner, repo = _detect_owner_repo()
    todo_state_id = _linear_find_state_id(linear_token, team_id=linear_team_id, state_name=todo_state_name)

    prs = _list_closed_prs(
        github_token,
        owner=owner,
        repo=repo,
        base_branch=base_branch,
        head_branch_prefix=head_branch_prefix,
        lookback_hours=lookback_hours,
        max_prs=max_prs,
    )
    if verbose:
        print(f"scan: {len(prs)} closed PR(s) targeting {owner}/{repo}:{base_branch}", file=sys.stderr)

    updated = 0
    skipped = 0

    for pr in prs:
        if pr.merged_at:
            continue

        try:
            state, state_reason, issue_updated_at = _issue_state_reason(
                github_token, owner=owner, repo=repo, issue_number=pr.number
            )
        except Exception as e:
            print(f"warn: failed to read close reason for PR #{pr.number}: {e}", file=sys.stderr)
            continue

        if state != "closed":
            continue
        if state_reason != "not_planned":
            continue

        prev = _db_get(conn, pr.number)
        if prev:
            prev_updated_at, _prev_status = prev
            if issue_updated_at and prev_updated_at and issue_updated_at <= prev_updated_at:
                skipped += 1
                continue

        cands = _extract_linear_ids(pr.title, pr.head_ref)
        linear_id = _pick_linear_id(cands, prefer_team_key=prefer_team_key)
        if not linear_id:
            msg = f"no Linear id found in title/head_ref (candidates={cands})"
            _db_put(conn, pr_number=pr.number, pr_updated_at=issue_updated_at or pr.updated_at, status="skipped", message=msg)
            if verbose:
                print(f"skip #{pr.number}: {msg}", file=sys.stderr)
            continue

        issue = _linear_fetch_issue(linear_token, identifier=linear_id)
        if not issue:
            msg = f"Linear issue not found: {linear_id}"
            _db_put(conn, pr_number=pr.number, pr_updated_at=issue_updated_at or pr.updated_at, status="skipped", linear_id=linear_id, message=msg)
            print(f"warn: #{pr.number}: {msg}", file=sys.stderr)
            continue

        input_obj: dict[str, Any] = {"stateId": todo_state_id}

        codex_sub = codex_name_substr.strip().lower()
        if clear_assignee and issue.assignee_id:
            name = (issue.assignee_name or "").lower()
            if not codex_sub or (codex_sub in name):
                input_obj["assigneeId"] = None

        if clear_delegate and issue.delegate_id:
            name = (issue.delegate_name or "").lower()
            if not codex_sub or (codex_sub in name):
                input_obj["delegateId"] = None

        if dry_run:
            updated += 1
            print(
                f"dry-run: would reset {linear_id} to {todo_state_name} and clear codex assignment (PR #{pr.number})",
                file=sys.stderr,
            )
            _db_put(
                conn,
                pr_number=pr.number,
                pr_updated_at=issue_updated_at or pr.updated_at,
                status="dry-run",
                linear_id=linear_id,
            )
            continue

        try:
            try:
                _linear_issue_update(linear_token, issue_id=issue.id, input_obj=input_obj)
            except Exception as e:
                # If the workspace doesn't support delegate unassignment via API, still reset state to Todo.
                msg = str(e)
                did_retry = False
                if "delegateId" in input_obj and ("delegateId" in msg or "delegate" in msg):
                    input_obj.pop("delegateId", None)
                    did_retry = True
                if "assigneeId" in input_obj and ("assigneeId" in msg or "assignee" in msg):
                    input_obj.pop("assigneeId", None)
                    did_retry = True
                if not did_retry:
                    raise
                _linear_issue_update(linear_token, issue_id=issue.id, input_obj=input_obj)
                if verbose:
                    print(
                        f"warn: Linear schema rejected delegate/assignee unassignment; only reset {linear_id} to {todo_state_name}",
                        file=sys.stderr,
                    )
            updated += 1
            _db_put(
                conn,
                pr_number=pr.number,
                pr_updated_at=issue_updated_at or pr.updated_at,
                status="updated",
                linear_id=linear_id,
            )
            print(f"updated {linear_id}: reset to {todo_state_name} (from PR #{pr.number})", file=sys.stderr)
        except Exception as e:
            msg = str(e)[:500]
            _db_put(
                conn,
                pr_number=pr.number,
                pr_updated_at=issue_updated_at or pr.updated_at,
                status="error",
                linear_id=linear_id,
                message=msg,
            )
            print(f"warn: failed to update {linear_id} from PR #{pr.number}: {e}", file=sys.stderr)

    if verbose:
        print(f"done: updated={updated} skipped={skipped}", file=sys.stderr)
    return 0


def main(argv: list[str]) -> int:
    _load_dotenv(REPO_ROOT / ".env")

    parser = argparse.ArgumentParser(
        description=(
            "GitHub → Linear backflow: when a PR is closed as 'not planned', reset the linked Linear issue to Todo "
            "and unassign Codex.\n\n"
            "Linking: the script looks for a Linear id like 'TVM-1234' in the PR title and head branch name."
        )
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--once", action="store_true", help="Run a single scan/update cycle.")
    mode.add_argument("--watch", action="store_true", help="Run forever, scanning periodically.")

    parser.add_argument("--interval-seconds", type=int, default=60, help="Polling interval for --watch (default: 60).")
    parser.add_argument("--state", default=str(REPO_ROOT / ".autopr" / "linear_backflow.sqlite3"), help="SQLite state DB path.")

    parser.add_argument("--target-branch", default=DEFAULT_TARGET_BRANCH, help=f"Target base branch (default: {DEFAULT_TARGET_BRANCH}).")
    parser.add_argument(
        "--head-branch-prefix",
        default=DEFAULT_HEAD_BRANCH_PREFIX,
        help=f"Only consider PRs whose head branch starts with this prefix (default: {DEFAULT_HEAD_BRANCH_PREFIX!r}). Use '' to disable.",
    )
    parser.add_argument("--lookback-hours", type=float, default=DEFAULT_LOOKBACK_HOURS, help="Only scan PRs updated recently.")
    parser.add_argument("--max-prs", type=int, default=250, help="Max PRs to scan per cycle (default: 250).")

    parser.add_argument("--linear-team-id", default=LINEAR_TEAM_ID, help="Linear team id used to resolve the Todo state.")
    parser.add_argument("--todo-state-name", default=DEFAULT_TODO_STATE_NAME, help="Linear workflow state name to reset to.")
    parser.add_argument("--prefer-team-key", default=DEFAULT_TEAM_KEY, help="Prefer a matching Linear team key when multiple ids are present.")
    parser.add_argument(
        "--codex-name-substr",
        default=DEFAULT_CODEX_NAME_SUBSTR,
        help="Only clear assignee/delegate if their name contains this substring (case-insensitive). Use '' to clear unconditionally.",
    )
    parser.add_argument("--clear-assignee", action=argparse.BooleanOptionalAction, default=True, help="Clear assignee if it looks like Codex.")
    parser.add_argument("--clear-delegate", action=argparse.BooleanOptionalAction, default=True, help="Clear delegate if it looks like Codex.")

    parser.add_argument("--dry-run", action="store_true", help="Print actions without updating Linear.")
    parser.add_argument("--verbose", action="store_true", help="Verbose logs to stderr.")

    parser.add_argument(
        "--github-token",
        default="",
        help="GitHub token (optional). If omitted, uses GITHUB_TOKEN/GH_TOKEN or falls back to `gh auth token`.",
    )
    parser.add_argument("--linear-token", default=os.environ.get("LINEAR_API_KEY") or "", help="Linear API key.")

    args = parser.parse_args(argv)

    github_token = args.github_token.strip() or os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN") or ""
    if not github_token:
        # Convenience fallback: reuse `gh` auth if available.
        try:
            github_token = subprocess.check_output(["gh", "auth", "token"], text=True).strip()
        except Exception:
            github_token = ""
    if not github_token:
        print(
            "error: missing GitHub token (set GITHUB_TOKEN/GH_TOKEN, or authenticate via `gh auth login`).",
            file=sys.stderr,
        )
        return 2

    linear_token = args.linear_token.strip()
    if not linear_token:
        print("error: missing Linear API key (set LINEAR_API_KEY).", file=sys.stderr)
        return 2

    head_prefix = args.head_branch_prefix
    # Allow explicit empty string from CLI ('') as "no filter".
    if head_prefix == "''" or head_prefix == '""':
        head_prefix = ""

    conn = _db_connect(Path(args.state))

    def once():
        return run_once(
            conn=conn,
            github_token=github_token,
            linear_token=linear_token,
            linear_team_id=str(args.linear_team_id),
            base_branch=str(args.target_branch),
            head_branch_prefix=str(head_prefix),
            lookback_hours=float(args.lookback_hours),
            max_prs=int(args.max_prs),
            todo_state_name=str(args.todo_state_name),
            prefer_team_key=str(args.prefer_team_key),
            codex_name_substr=str(args.codex_name_substr),
            clear_assignee=bool(args.clear_assignee),
            clear_delegate=bool(args.clear_delegate),
            dry_run=bool(args.dry_run),
            verbose=bool(args.verbose),
        )

    if args.once:
        return once()

    interval = max(10, int(args.interval_seconds))
    while True:
        try:
            once()
        except KeyboardInterrupt:
            return 130
        except Exception as e:
            print(f"warn: cycle failed: {e}", file=sys.stderr)
        time.sleep(interval)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
