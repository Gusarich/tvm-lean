#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]

GITHUB_API = "https://api.github.com"
GITHUB_GRAPHQL = "https://api.github.com/graphql"

DEFAULT_TARGET_BRANCH = "main"
DEFAULT_HEAD_BRANCH_PREFIX = "codex/"
DEFAULT_BOT_LOGIN = "chatgpt-codex-connector[bot]"
DEFAULT_REQUIRED_CHECKS = ("Lean", "Collector (TypeScript)")


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
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "X-GitHub-Api-Version": "2022-11-28",
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


def _graphql(token: str, query: str, variables: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = {"query": query, "variables": variables or {}}
    data = _http_json(token, GITHUB_GRAPHQL, method="POST", body=payload)
    if not isinstance(data, dict):
        raise RuntimeError(f"unexpected GraphQL response type: {type(data)}")
    if "errors" in data:
        raise RuntimeError(f"GitHub GraphQL errors: {data['errors']}")
    out = data.get("data")
    if not isinstance(out, dict):
        return {}
    return out


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
        # Accept "owner/repo" or "host/owner/repo"
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

    # Examples:
    # - git@github.com:OWNER/REPO.git
    # - https://github.com/OWNER/REPO.git
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


@dataclass(frozen=True)
class PullRequest:
    id: str
    number: int
    title: str
    url: str
    is_draft: bool
    head_ref: str
    head_oid: str
    mergeable: str
    merge_state_status: str
    contexts: list[dict[str, Any]]


def _parse_pr(node: dict[str, Any]) -> PullRequest | None:
    try:
        pr_id = str(node["id"])
        number = int(node["number"])
        title = str(node.get("title") or "")
        url = str(node.get("url") or "")
        is_draft = bool(node.get("isDraft"))
        head_ref = str(node.get("headRefName") or "")
        head_oid = str(node.get("headRefOid") or "")
        mergeable = str(node.get("mergeable") or "")
        merge_state_status = str(node.get("mergeStateStatus") or "")

        rollup = (
            (((node.get("commits") or {}).get("nodes") or [None])[0] or {}).get("commit") or {}
        ).get("statusCheckRollup")
        contexts = ((rollup or {}).get("contexts") or {}).get("nodes") or []
        if not isinstance(contexts, list):
            contexts = []

        return PullRequest(
            id=pr_id,
            number=number,
            title=title,
            url=url,
            is_draft=is_draft,
            head_ref=head_ref,
            head_oid=head_oid,
            mergeable=mergeable,
            merge_state_status=merge_state_status,
            contexts=contexts,
        )
    except Exception:
        return None


def _list_open_prs(token: str, *, owner: str, repo: str, base_branch: str) -> list[PullRequest]:
    query = """
    query($owner:String!,$repo:String!,$base:String!,$cursor:String){
      repository(owner:$owner,name:$repo){
        pullRequests(
          first:100,
          after:$cursor,
          states:OPEN,
          baseRefName:$base,
          orderBy:{field:CREATED_AT,direction:ASC}
        ){
          nodes{
            id
            number
            title
            url
            isDraft
            headRefName
            headRefOid
            mergeable
            mergeStateStatus
            commits(last:1){
              nodes{
                commit{
                  oid
                  statusCheckRollup{
                    contexts(last:100){
                      nodes{
                        __typename
                        ... on CheckRun{
                          name
                          status
                          conclusion
                          startedAt
                          completedAt
                        }
                        ... on StatusContext{
                          context
                          state
                          createdAt
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          pageInfo{hasNextPage endCursor}
        }
      }
    }
    """
    prs: list[PullRequest] = []
    cursor: str | None = None
    while True:
        data = _maybe_retry(lambda: _graphql(token, query, {"owner": owner, "repo": repo, "base": base_branch, "cursor": cursor}))
        page = ((data.get("repository") or {}).get("pullRequests") or {})
        for node in (page.get("nodes") or []) or []:
            if not isinstance(node, dict):
                continue
            pr = _parse_pr(node)
            if pr:
                prs.append(pr)
        info = page.get("pageInfo") or {}
        if not info.get("hasNextPage"):
            break
        cursor = info.get("endCursor")
        if not isinstance(cursor, str) or not cursor:
            break
    return prs


def _update_pr_branch(token: str, *, pr_id: str, expected_head_oid: str) -> None:
    mutation = """
    mutation($prId:ID!,$expected:GitObjectID!){
      updatePullRequestBranch(input:{pullRequestId:$prId,expectedHeadOid:$expected}){
        pullRequest{number}
      }
    }
    """
    _maybe_retry(lambda: _graphql(token, mutation, {"prId": pr_id, "expected": expected_head_oid}))


def _merge_pr_squash(token: str, *, pr_id: str, expected_head_oid: str) -> bool:
    mutation = """
    mutation($prId:ID!,$expected:GitObjectID!){
      mergePullRequest(input:{pullRequestId:$prId,mergeMethod:SQUASH,expectedHeadOid:$expected}){
        pullRequest{number merged mergedAt}
      }
    }
    """
    data = _maybe_retry(lambda: _graphql(token, mutation, {"prId": pr_id, "expected": expected_head_oid}))
    pr = ((data.get("mergePullRequest") or {}).get("pullRequest") or {})
    return bool(pr.get("merged"))


@dataclass(frozen=True)
class PullRequestMergeMeta:
    id: str
    number: int
    head_ref: str
    head_oid: str
    is_draft: bool
    mergeable: str
    merge_state_status: str


def _fetch_pr_merge_meta(token: str, *, owner: str, repo: str, number: int) -> PullRequestMergeMeta | None:
    query = """
    query($owner:String!,$repo:String!,$number:Int!){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$number){
          id
          number
          isDraft
          headRefName
          headRefOid
          mergeable
          mergeStateStatus
        }
      }
    }
    """
    data = _maybe_retry(lambda: _graphql(token, query, {"owner": owner, "repo": repo, "number": number}))
    pr = ((data.get("repository") or {}).get("pullRequest") or {})
    if not isinstance(pr, dict) or not pr.get("id"):
        return None
    try:
        return PullRequestMergeMeta(
            id=str(pr["id"]),
            number=int(pr["number"]),
            head_ref=str(pr.get("headRefName") or ""),
            head_oid=str(pr.get("headRefOid") or ""),
            is_draft=bool(pr.get("isDraft")),
            mergeable=str(pr.get("mergeable") or ""),
            merge_state_status=str(pr.get("mergeStateStatus") or ""),
        )
    except Exception:
        return None


def _list_issue_reactions(
    token: str, *, owner: str, repo: str, issue_number: int, per_page: int = 100
) -> Iterable[dict[str, Any]]:
    url = f"{GITHUB_API}/repos/{owner}/{repo}/issues/{issue_number}/reactions"
    page = 1
    while True:
        data = _maybe_retry(lambda: _http_json(token, url, params={"per_page": per_page, "page": page}))
        if not isinstance(data, list):
            return
        if not data:
            return
        for item in data:
            if isinstance(item, dict):
                yield item
        if len(data) < per_page:
            return
        page += 1


def _codex_approval_state(
    token: str,
    *,
    owner: str,
    repo: str,
    pr_number: int,
    bot_login: str,
) -> str:
    # Returns: "approved" | "rejected" | "missing"
    has_plus = False
    has_minus = False
    for r in _list_issue_reactions(token, owner=owner, repo=repo, issue_number=pr_number):
        user = (r.get("user") or {}).get("login")
        content = r.get("content")
        if user != bot_login:
            continue
        if content == "+1":
            has_plus = True
        if content == "-1":
            has_minus = True
    if has_plus:
        return "approved"
    if has_minus:
        return "rejected"
    return "missing"


def _latest_context_by_name(contexts: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}

    def ts_for(entry: dict[str, Any]) -> str:
        if entry.get("kind") == "check":
            return str(entry.get("completedAt") or entry.get("startedAt") or "")
        return str(entry.get("createdAt") or "")

    for ctx in contexts:
        typ = ctx.get("__typename")
        if typ == "CheckRun":
            name = ctx.get("name")
            if not isinstance(name, str) or not name:
                continue
            cand = {
                "kind": "check",
                "name": name,
                "status": ctx.get("status"),
                "conclusion": ctx.get("conclusion"),
                "startedAt": ctx.get("startedAt"),
                "completedAt": ctx.get("completedAt"),
            }
        elif typ == "StatusContext":
            name = ctx.get("context")
            if not isinstance(name, str) or not name:
                continue
            cand = {
                "kind": "status",
                "name": name,
                "state": ctx.get("state"),
                "createdAt": ctx.get("createdAt"),
            }
        else:
            continue

        prev = out.get(name)
        if not prev or ts_for(cand) > ts_for(prev):
            out[name] = cand

    return out


def _required_checks_state(
    contexts: list[dict[str, Any]],
    required: tuple[str, ...],
) -> tuple[list[str], list[str], list[str]]:
    by_name = _latest_context_by_name(contexts)
    missing: list[str] = []
    pending: list[str] = []
    failing: list[str] = []

    for name in required:
        entry = by_name.get(name)
        if not entry:
            missing.append(name)
            continue
        if entry["kind"] == "check":
            status = entry.get("status")
            conclusion = entry.get("conclusion")
            if status != "COMPLETED":
                pending.append(name)
            elif conclusion != "SUCCESS":
                failing.append(name)
        else:
            state = entry.get("state")
            if state == "PENDING":
                pending.append(name)
            elif state != "SUCCESS":
                failing.append(name)

    return missing, pending, failing


def _cycle(
    token: str,
    *,
    owner: str,
    repo: str,
    base_branch: str,
    required_checks: tuple[str, ...],
    head_branch_prefix: str,
    update_behind: bool,
    require_codex_approval: bool,
    codex_bot_login: str,
    max_merges: int,
    max_updates: int,
    dry_run: bool,
    verbose: bool,
) -> None:
    prs = _list_open_prs(token, owner=owner, repo=repo, base_branch=base_branch)
    if verbose:
        print(f"scan: {len(prs)} open PR(s) targeting {owner}/{repo}:{base_branch}", file=sys.stderr)

    merged = 0
    updated = 0

    for pr in prs:
        if merged >= max_merges:
            break

        if pr.is_draft:
            continue

        if head_branch_prefix and not pr.head_ref.startswith(head_branch_prefix):
            continue

        missing, pending, failing = _required_checks_state(pr.contexts, required_checks)
        if missing or pending or failing:
            if verbose:
                parts = []
                if missing:
                    parts.append(f"missing={','.join(missing)}")
                if pending:
                    parts.append(f"pending={','.join(pending)}")
                if failing:
                    parts.append(f"failing={','.join(failing)}")
                print(f"skip #{pr.number}: checks not ready ({'; '.join(parts)})", file=sys.stderr)
            continue

        if require_codex_approval:
            try:
                approval = _codex_approval_state(
                    token,
                    owner=owner,
                    repo=repo,
                    pr_number=pr.number,
                    bot_login=codex_bot_login,
                )
            except Exception as e:
                print(f"warn: failed to read reactions for #{pr.number}: {e}", file=sys.stderr)
                continue

            if approval != "approved":
                if verbose:
                    print(f"skip #{pr.number}: codex approval={approval}", file=sys.stderr)
                continue

        meta = _fetch_pr_merge_meta(token, owner=owner, repo=repo, number=pr.number)
        if not meta:
            print(f"warn: failed to load merge meta for #{pr.number}", file=sys.stderr)
            continue

        if meta.is_draft:
            continue

        if head_branch_prefix and not meta.head_ref.startswith(head_branch_prefix):
            continue

        if meta.merge_state_status == "DIRTY":
            if verbose:
                print(f"skip #{pr.number}: conflicts (DIRTY)", file=sys.stderr)
            continue

        if meta.merge_state_status == "BEHIND":
            if not update_behind or updated >= max_updates:
                if verbose:
                    print(f"skip #{pr.number}: behind {base_branch}", file=sys.stderr)
                continue
            if dry_run:
                updated += 1
                if verbose:
                    print(f"dry-run update #{pr.number}: would trigger branch update", file=sys.stderr)
            else:
                try:
                    _update_pr_branch(token, pr_id=meta.id, expected_head_oid=meta.head_oid)
                    updated += 1
                    if verbose:
                        print(f"update #{pr.number}: triggered branch update", file=sys.stderr)
                except Exception as e:
                    print(f"warn: failed to update #{pr.number}: {e}", file=sys.stderr)
            continue

        if meta.mergeable != "MERGEABLE":
            if verbose:
                print(f"skip #{pr.number}: mergeable={meta.mergeable}", file=sys.stderr)
            continue

        if dry_run:
            merged += 1
            print(f"dry-run merge #{pr.number}: would merge (SQUASH): {pr.title}", file=sys.stderr)
            continue

        try:
            ok = _merge_pr_squash(token, pr_id=meta.id, expected_head_oid=meta.head_oid)
        except Exception as e:
            print(f"warn: merge failed for #{pr.number}: {e}", file=sys.stderr)
            continue

        if ok:
            merged += 1
            print(f"merged #{pr.number}: {pr.title}", file=sys.stderr)
        else:
            print(f"warn: merge mutation returned merged=false for #{pr.number}", file=sys.stderr)

    if verbose:
        print(f"done: merged={merged} updated={updated}", file=sys.stderr)


def _parse_required_checks(raw: str | None) -> tuple[str, ...]:
    if not raw:
        return tuple(DEFAULT_REQUIRED_CHECKS)
    out = [s.strip() for s in raw.split(",") if s.strip()]
    return tuple(out) if out else tuple(DEFAULT_REQUIRED_CHECKS)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Auto-merge eligible PRs (local daemon).")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--once", action="store_true", help="Run a single scan/merge cycle.")
    mode.add_argument("--watch", action="store_true", help="Run forever, scanning periodically.")

    parser.add_argument("--interval-seconds", type=int, default=60, help="Polling interval for --watch (default: 60).")
    parser.add_argument("--target-branch", default=DEFAULT_TARGET_BRANCH, help=f"Target base branch (default: {DEFAULT_TARGET_BRANCH}).")
    parser.add_argument(
        "--head-branch-prefix",
        default=DEFAULT_HEAD_BRANCH_PREFIX,
        help=f"Only consider PRs whose head branch starts with this prefix (default: {DEFAULT_HEAD_BRANCH_PREFIX!r}). Use '' to disable.",
    )
    parser.add_argument(
        "--required-checks",
        default=",".join(DEFAULT_REQUIRED_CHECKS),
        help="Comma-separated list of required check names (job names / status contexts).",
    )
    parser.add_argument(
        "--update-behind",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="If a PR is behind base, attempt to update its branch and re-check later.",
    )
    parser.add_argument(
        "--require-codex-approval",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Require a +1 reaction from the Codex connector bot before merging.",
    )
    parser.add_argument(
        "--codex-bot-login",
        default=DEFAULT_BOT_LOGIN,
        help=f"GitHub login of the Codex review bot (default: {DEFAULT_BOT_LOGIN}).",
    )
    parser.add_argument("--max-merges", type=int, default=10, help="Max merges per cycle (default: 10).")
    parser.add_argument("--max-updates", type=int, default=25, help="Max branch updates per cycle (default: 25).")
    parser.add_argument("--dry-run", action="store_true", help="Print what would happen without updating branches or merging.")
    parser.add_argument("--verbose", action="store_true", help="Log decisions to stderr.")

    args = parser.parse_args(argv)

    _load_dotenv(REPO_ROOT / ".env")

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        # Convenience fallback: reuse `gh` auth if available.
        try:
            token = subprocess.check_output(["gh", "auth", "token"], text=True).strip()
        except Exception:
            token = None
    if not token:
        print("error: set GITHUB_TOKEN (or GH_TOKEN) in your environment or .env", file=sys.stderr)
        return 2

    owner, repo = _detect_owner_repo()
    required_checks = _parse_required_checks(args.required_checks)

    head_prefix = args.head_branch_prefix
    # Allow explicit empty string from CLI ('') as "no filter".
    if head_prefix == "''" or head_prefix == '""':
        head_prefix = ""

    def run_once():
        _cycle(
            token,
            owner=owner,
            repo=repo,
            base_branch=str(args.target_branch),
            required_checks=required_checks,
            head_branch_prefix=str(head_prefix),
            update_behind=bool(args.update_behind),
            require_codex_approval=bool(args.require_codex_approval),
            codex_bot_login=str(args.codex_bot_login),
            max_merges=int(args.max_merges),
            max_updates=int(args.max_updates),
            dry_run=bool(args.dry_run),
            verbose=bool(args.verbose),
        )

    if args.once:
        run_once()
        return 0

    interval = max(5, int(args.interval_seconds))
    while True:
        try:
            run_once()
        except KeyboardInterrupt:
            return 130
        except Exception as e:
            print(f"warn: cycle failed: {e}", file=sys.stderr)
        time.sleep(interval)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
