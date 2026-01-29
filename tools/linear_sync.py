#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any


GRAPHQL_URL = "https://api.linear.app/graphql"

# NOTE: These IDs are workspace-specific. If you migrate the Linear workspace, update this map.
TEAM_ID = "5c9dcc9f-5d33-4a9e-8fc2-b568b75a1edd"  # TVM Formal Verification
PROJECT_ID = "ee1015c4-d885-4426-9277-da0bb9bdf53e"  # Instruction Coverage (TVM Spec)

EPIC_ID = "c123817e-2383-4d74-b6c4-dfc28b06bd20"  # TVM-7

CATEGORY_PARENT_IDS: dict[str, str] = {
    "arithmetic": "e11c9088-0956-4cb4-841f-034907135f34",
    "cell": "7efb5b3f-afef-4523-8c57-5363f6f5ff0b",
    "dictionary": "8b142fd0-fcb7-4013-b905-6223cb2cf3a5",
    "continuation": "809d46b4-2f33-491b-a4c8-49939f88b0d0",
    "stack": "6e40577f-49a3-4874-842e-3642998627ea",
    "crypto": "7193c84b-763d-49d3-9021-cb6c324d549e",
    "config": "320ec105-da2b-4e91-b67d-7aec34f46223",
    "tuple": "dbec5e60-e1e2-4e5b-afb1-fe602507d65f",
    "exception": "04c5de7a-5164-4752-985f-5859d4026346",
    "debug": "ea42c4fb-3965-4e09-bf36-e314f58e2588",
    "message": "24d96a8c-6a4e-48d0-a8e3-c038026c78be",
    "address": "eea1227a-00cc-4a10-b149-8a52634dedc1",
    "basic_gas": "ec62a0e7-d387-4374-8c2f-73684fd95065",
    "globals": "400c3828-7ef3-4851-a644-cd22e4ded598",
    "prng": "30c86c07-6a27-4b69-94a4-0da70463f2a1",
    "misc": "21dd7504-ea2f-4d01-8569-61b279d57f87",
    "codepage": "b3f9f5d9-d127-4b85-9e26-5c57dcdf453c",
}

FIFT_ALIAS_PARENT_ID = "9f52e07c-0c92-47b5-abad-d17e533f2a3b"  # TVM-25

SPEC_KEY_RE = re.compile(r"(?m)^[ \t]*SpecKey:[ \t]*([^\s]+)[ \t]*$")

REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class LinearIssue:
    id: str
    title: str
    description: str | None
    parent_id: str | None
    project_id: str | None
    label_names: frozenset[str]


def _graphql(token: str, query: str, variables: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = {"query": query, "variables": variables or {}}
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        GRAPHQL_URL,
        data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": token,
        },
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
    return data.get("data") or {}


def _maybe_retry(fn, *, max_tries: int = 6, base_sleep_s: float = 0.5):
    last_err: Exception | None = None
    for i in range(max_tries):
        try:
            return fn()
        except Exception as e:
            last_err = e
            sleep_s = base_sleep_s * (2**i)
            time.sleep(sleep_s)
    assert last_err is not None
    raise last_err


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


def _load_spec_index(path: str) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def _extract_spec_key(description: str | None) -> str | None:
    if not description:
        return None
    m = SPEC_KEY_RE.search(description)
    return m.group(1) if m else None


def _fetch_label_ids(token: str) -> dict[str, str]:
    query = """
    query Labels($teamId: ID!) {
      issueLabels(first: 250, filter: { team: { id: { eq: $teamId } } }) {
        nodes { id name }
      }
    }
    """
    data = _maybe_retry(lambda: _graphql(token, query, {"teamId": TEAM_ID}))
    out: dict[str, str] = {}
    for node in (data.get("issueLabels", {}) or {}).get("nodes", []) or []:
        name = node.get("name")
        lid = node.get("id")
        if isinstance(name, str) and isinstance(lid, str):
            out[name] = lid
    return out


def _fetch_project_issues(token: str) -> dict[str, LinearIssue]:
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
          title
          description
          parent { id }
          project { id }
          labels { nodes { name } }
        }
      }
    }
    """
    by_spec_key: dict[str, LinearIssue] = {}
    after: str | None = None
    while True:
        vars: dict[str, Any] = {"teamId": TEAM_ID, "projectId": PROJECT_ID, "after": after}
        data = _maybe_retry(lambda: _graphql(token, query, vars))
        issues = (data.get("issues", {}) or {}).get("nodes", []) or []
        for node in issues:
            issue = LinearIssue(
                id=node["id"],
                title=node.get("title") or "",
                description=node.get("description"),
                parent_id=(node.get("parent") or {}).get("id"),
                project_id=(node.get("project") or {}).get("id"),
                label_names=frozenset(
                    (lbl.get("name") for lbl in ((node.get("labels") or {}).get("nodes") or []) if lbl.get("name"))
                ),
            )
            spec_key = _extract_spec_key(issue.description)
            if spec_key:
                by_spec_key[spec_key] = issue

        page_info = (data.get("issues", {}) or {}).get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        after = page_info.get("endCursor")
        if not after:
            break
    return by_spec_key


def _fetch_project_issues_all(token: str) -> list[LinearIssue]:
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
          title
          description
          parent { id }
          project { id }
          labels { nodes { name } }
        }
      }
    }
    """
    out: list[LinearIssue] = []
    after: str | None = None
    while True:
        vars: dict[str, Any] = {"teamId": TEAM_ID, "projectId": PROJECT_ID, "after": after}
        data = _maybe_retry(lambda: _graphql(token, query, vars))
        issues = (data.get("issues", {}) or {}).get("nodes", []) or []
        for node in issues:
            out.append(
                LinearIssue(
                    id=node["id"],
                    title=node.get("title") or "",
                    description=node.get("description"),
                    parent_id=(node.get("parent") or {}).get("id"),
                    project_id=(node.get("project") or {}).get("id"),
                    label_names=frozenset(
                        (
                            lbl.get("name")
                            for lbl in ((node.get("labels") or {}).get("nodes") or [])
                            if lbl.get("name")
                        )
                    ),
                )
            )

        page_info = (data.get("issues", {}) or {}).get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        after = page_info.get("endCursor")
        if not after:
            break
    return out


def _issue_create(
    token: str,
    *,
    title: str,
    description: str,
    parent_id: str,
    label_ids: list[str],
) -> str:
    mutation = """
    mutation IssueCreate($input: IssueCreateInput!) {
      issueCreate(input: $input) {
        success
        issue { id identifier }
      }
    }
    """
    input_obj = {
        "teamId": TEAM_ID,
        "projectId": PROJECT_ID,
        "parentId": parent_id,
        "title": title,
        "description": description,
        "labelIds": label_ids,
    }
    data = _maybe_retry(lambda: _graphql(token, mutation, {"input": input_obj}))
    created = (data.get("issueCreate") or {}).get("issue") or {}
    issue_id = created.get("id")
    if not isinstance(issue_id, str):
        raise RuntimeError(f"issueCreate did not return an id: {data}")
    return issue_id


def _issue_update(
    token: str,
    issue_id: str,
    *,
    parent_id: str | None = None,
    label_ids: list[str] | None = None,
    project_id: str | None = None,
    title: str | None = None,
    description: str | None = None,
) -> None:
    mutation = """
    mutation IssueUpdate($id: String!, $input: IssueUpdateInput!) {
      issueUpdate(id: $id, input: $input) {
        success
        issue { id }
      }
    }
    """
    input_obj: dict[str, Any] = {}
    if parent_id is not None:
        input_obj["parentId"] = parent_id
    if label_ids is not None:
        input_obj["labelIds"] = label_ids
    if project_id is not None:
        input_obj["projectId"] = project_id
    if title is not None:
        input_obj["title"] = title
    if description is not None:
        input_obj["description"] = description

    if not input_obj:
        return

    _maybe_retry(lambda: _graphql(token, mutation, {"id": issue_id, "input": input_obj}))


def _required_label_names_for_tvm(category: str) -> list[str]:
    return ["kind/tvm", f"cat/{category}"]


def _required_label_names_for_fift(actual_category: str | None) -> list[str]:
    out = ["kind/fift-alias"]
    if actual_category:
        out.append(f"cat/{actual_category}")
    return out


def _format_category(category: str, sub_category: str | None) -> str:
    if sub_category:
        return f"{category} / {sub_category}"
    return category


def _tvm_issue_description(it: dict[str, Any], *, spec_key: str) -> str:
    name = it.get("name") if isinstance(it.get("name"), str) else ""
    category = it.get("category") if isinstance(it.get("category"), str) else ""
    sub_category = it.get("sub_category") if isinstance(it.get("sub_category"), str) else ""
    short = it.get("short") if isinstance(it.get("short"), str) else ""
    signature = it.get("signature_stack_string") if isinstance(it.get("signature_stack_string"), str) else ""
    layout = it.get("layout") if isinstance(it.get("layout"), dict) else {}
    impl = it.get("implementation") if isinstance(it.get("implementation"), dict) else {}

    lines: list[str] = [f"SpecKey: {spec_key}"]

    if category:
        lines.append("")
        lines.append(f"Category: {_format_category(category, sub_category or None)}")
    if signature:
        lines.append(f"Signature: {signature}")
    if short:
        lines.append(f"Short: {short}")

    if layout:
        lines.append("")
        lines.append("Encoding:")
        for k in ("kind", "prefix_str", "checkLen", "skipLen", "tlb"):
            v = layout.get(k)
            if v is None or v == "":
                continue
            lines.append(f"- {k}: {v}")

    if impl:
        commit = impl.get("commit_hash")
        file_path = impl.get("file_path")
        line_number = impl.get("line_number")
        function_name = impl.get("function_name")
        if commit or file_path or line_number or function_name:
            lines.append("")
            lines.append("TON ref:")
            if commit:
                lines.append(f"- ton-blockchain/ton@{commit}")
            if file_path and line_number and function_name:
                lines.append(f"- {file_path}:{line_number} ({function_name})")
            elif file_path and line_number:
                lines.append(f"- {file_path}:{line_number}")
            elif file_path:
                lines.append(f"- {file_path}")

    lines.append("")
    lines.append("Checklist:")
    lines.append("- [ ] Spec audit vs C++")
    lines.append("- [ ] Implement semantics in Lean")
    lines.append("- [ ] Tests")
    lines.append("- [ ] Diff tests")
    lines.append("- [ ] Proof (if needed)")

    # Avoid trailing whitespace / ensure a final newline in Linear's renderer.
    return "\n".join(lines).rstrip() + "\n"


def _fift_issue_description(
    it: dict[str, Any],
    *,
    spec_key: str,
    tvm_by_name: dict[str, dict[str, Any]],
) -> str:
    alias = it.get("name") if isinstance(it.get("name"), str) else ""
    actual = it.get("actual_name") if isinstance(it.get("actual_name"), str) else ""
    actual_category = it.get("actual_category") if isinstance(it.get("actual_category"), str) else ""

    lines: list[str] = [f"SpecKey: {spec_key}"]
    lines.append("")
    lines.append(f"Alias: {alias}")
    lines.append(f"Expands to: tvm::{actual}")
    if actual_category:
        lines.append(f"Actual category: {actual_category}")

    actual_row = tvm_by_name.get(actual) if actual else None
    impl = actual_row.get("implementation") if isinstance(actual_row, dict) else None
    if isinstance(impl, dict) and impl:
        commit = impl.get("commit_hash")
        file_path = impl.get("file_path")
        line_number = impl.get("line_number")
        function_name = impl.get("function_name")
        lines.append("")
        lines.append("TON ref (actual instruction):")
        if commit:
            lines.append(f"- ton-blockchain/ton@{commit}")
        if file_path and line_number and function_name:
            lines.append(f"- {file_path}:{line_number} ({function_name})")
        elif file_path and line_number:
            lines.append(f"- {file_path}:{line_number}")
        elif file_path:
            lines.append(f"- {file_path}")

    lines.append("")
    lines.append("Checklist:")
    lines.append("- [ ] Verify alias matches spec")
    lines.append("- [ ] Ensure decoder/pretty-printer handles alias")
    lines.append("- [ ] Tests")
    return "\n".join(lines).rstrip() + "\n"


def _needs_tvm_description_update(existing_description: str | None, it: dict[str, Any], *, spec_key: str) -> bool:
    if not existing_description:
        return True
    if f"SpecKey: {spec_key}" not in existing_description:
        return True
    if "Checklist:" not in existing_description:
        return True
    if "Category:" not in existing_description:
        return True
    if "Encoding:" not in existing_description:
        return True

    impl = it.get("implementation")
    if isinstance(impl, dict) and impl:
        commit = impl.get("commit_hash")
        if isinstance(commit, str) and commit and commit not in existing_description:
            return True
    return False


def _needs_fift_description_update(existing_description: str | None, *, spec_key: str) -> bool:
    if not existing_description:
        return True
    if f"SpecKey: {spec_key}" not in existing_description:
        return True
    if "Checklist:" not in existing_description:
        return True
    if "Alias:" not in existing_description:
        return True
    if "Expands to:" not in existing_description:
        return True
    return False


def main() -> int:
    _load_dotenv(REPO_ROOT / ".env")

    parser = argparse.ArgumentParser(description="Sync Linear backlog issues from docs/progress/tvm_spec_index.json.")
    parser.add_argument(
        "--spec-index",
        default="docs/progress/tvm_spec_index.json",
        help="Path to generated spec index JSON (default: docs/progress/tvm_spec_index.json).",
    )
    parser.add_argument(
        "--token",
        default=os.getenv("LINEAR_API_KEY") or "",
        help="Linear API key (or set LINEAR_API_KEY env var).",
    )
    parser.add_argument("--apply", action="store_true", help="Actually create/update issues (default: dry-run).")
    parser.add_argument("--limit", type=int, default=0, help="Optional cap on number of creates (0 = no cap).")
    parser.add_argument(
        "--sync-descriptions",
        action="store_true",
        help="Update existing instruction descriptions to the canonical template when they look incomplete.",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="After syncing, verify that all tvm-spec index entries have a corresponding Linear issue.",
    )
    args = parser.parse_args()

    token = args.token.strip()
    if not token:
        print("Missing Linear API key. Provide --token or set LINEAR_API_KEY.", file=sys.stderr)
        return 2

    spec = _load_spec_index(args.spec_index)
    tvm_items = spec.get("tvm_instructions") or []
    fift_items = spec.get("fift_instructions") or []

    tvm_by_name: dict[str, dict[str, Any]] = {}
    for it in tvm_items:
        name = it.get("name")
        if isinstance(name, str):
            tvm_by_name[name] = it

    label_ids_by_name = _fetch_label_ids(token)
    existing_by_spec_key = _fetch_project_issues(token)

    def label_ids_for(names: list[str]) -> list[str]:
        missing = [n for n in names if n not in label_ids_by_name]
        if missing:
            raise RuntimeError(f"Missing Linear labels: {missing}")
        return [label_ids_by_name[n] for n in names]

    creates = 0
    updates = 0
    desc_updates = 0

    # TVM instructions
    for it in tvm_items:
        name = it.get("name")
        category = it.get("category")
        if not isinstance(name, str) or not isinstance(category, str):
            continue
        if category not in CATEGORY_PARENT_IDS:
            raise RuntimeError(f"Unknown category in spec index: {category}")

        spec_key = f"tvm::{name}"
        required_labels = _required_label_names_for_tvm(category)
        parent_id = CATEGORY_PARENT_IDS[category]

        existing = existing_by_spec_key.get(spec_key)
        if existing is None:
            if not args.apply:
                print(f"[create] Instr: {name} ({spec_key})")
            else:
                description = _tvm_issue_description(it, spec_key=spec_key)
                _issue_create(
                    token,
                    title=f"Instr: {name}",
                    description=description,
                    parent_id=parent_id,
                    label_ids=label_ids_for(required_labels),
                )
            creates += 1
        else:
            new_label_names = set(existing.label_names)
            new_label_names.update(required_labels)
            need_update = False
            update_label_ids: list[str] | None = None
            if parent_id != (existing.parent_id or ""):
                need_update = True
            if new_label_names != set(existing.label_names):
                need_update = True
                update_label_ids = label_ids_for(sorted(new_label_names))
            if (existing.project_id or "") != PROJECT_ID:
                need_update = True

            if need_update:
                if not args.apply:
                    print(f"[update] Instr: {name} ({spec_key})")
                else:
                    _issue_update(
                        token,
                        existing.id,
                        parent_id=parent_id,
                        label_ids=update_label_ids,
                        project_id=PROJECT_ID,
                    )
                updates += 1

            if args.sync_descriptions and _needs_tvm_description_update(existing.description, it, spec_key=spec_key):
                if not args.apply:
                    print(f"[update-desc] Instr: {name} ({spec_key})")
                else:
                    description = _tvm_issue_description(it, spec_key=spec_key)
                    _issue_update(token, existing.id, description=description)
                desc_updates += 1

        if args.limit and creates >= args.limit:
            break

    # Fift aliases
    if not args.limit or creates < args.limit:
        for it in fift_items:
            alias = it.get("name")
            actual = it.get("actual_name")
            actual_cat = it.get("actual_category")
            if not isinstance(alias, str) or not isinstance(actual, str):
                continue

            spec_key = f"fift::{alias}"
            required_labels = _required_label_names_for_fift(actual_cat if isinstance(actual_cat, str) else None)
            existing = existing_by_spec_key.get(spec_key)
            title = f"Fift: {alias} -> {actual}"

            if existing is None:
                if not args.apply:
                    print(f"[create] {title} ({spec_key})")
                else:
                    description = _fift_issue_description(it, spec_key=spec_key, tvm_by_name=tvm_by_name)
                    _issue_create(
                        token,
                        title=title,
                        description=description,
                        parent_id=FIFT_ALIAS_PARENT_ID,
                        label_ids=label_ids_for(required_labels),
                    )
                creates += 1
            else:
                new_label_names = set(existing.label_names)
                new_label_names.update(required_labels)
                need_update = False
                update_label_ids: list[str] | None = None
                if (existing.parent_id or "") != FIFT_ALIAS_PARENT_ID:
                    need_update = True
                if new_label_names != set(existing.label_names):
                    need_update = True
                    update_label_ids = label_ids_for(sorted(new_label_names))
                if (existing.project_id or "") != PROJECT_ID:
                    need_update = True
                if need_update:
                    if not args.apply:
                        print(f"[update] {title} ({spec_key})")
                    else:
                        _issue_update(
                            token,
                            existing.id,
                            parent_id=FIFT_ALIAS_PARENT_ID,
                            label_ids=update_label_ids,
                            project_id=PROJECT_ID,
                        )
                    updates += 1

                if args.sync_descriptions and _needs_fift_description_update(existing.description, spec_key=spec_key):
                    if not args.apply:
                        print(f"[update-desc] {title} ({spec_key})")
                    else:
                        description = _fift_issue_description(it, spec_key=spec_key, tvm_by_name=tvm_by_name)
                        _issue_update(token, existing.id, description=description)
                    desc_updates += 1

            if args.limit and creates >= args.limit:
                break

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"{mode}: creates={creates} updates={updates} desc_updates={desc_updates}")

    if args.verify:
        # Re-fetch after potential creates/updates.
        all_issues = _fetch_project_issues_all(token)
        spec_keys_to_issues: dict[str, list[LinearIssue]] = {}
        for issue in all_issues:
            spec_key = _extract_spec_key(issue.description)
            if not spec_key:
                continue
            spec_keys_to_issues.setdefault(spec_key, []).append(issue)

        expected_tvm: set[str] = set()
        for it in tvm_items:
            name = it.get("name")
            if isinstance(name, str) and name:
                expected_tvm.add(f"tvm::{name}")

        expected_fift: set[str] = set()
        for it in fift_items:
            name = it.get("name")
            if isinstance(name, str) and name:
                expected_fift.add(f"fift::{name}")

        found_tvm = {k for k in spec_keys_to_issues.keys() if k.startswith("tvm::")}
        found_fift = {k for k in spec_keys_to_issues.keys() if k.startswith("fift::")}
        missing_tvm = sorted(expected_tvm - found_tvm)
        missing_fift = sorted(expected_fift - found_fift)
        dup_keys = sorted(k for k, v in spec_keys_to_issues.items() if len(v) > 1)

        # Ignore category/meta keys for "extra" reporting.
        expected_all = expected_tvm | expected_fift
        extra_keys = sorted(
            k
            for k in spec_keys_to_issues.keys()
            if (k not in expected_all) and (not k.startswith("cat::"))
        )

        print(
            "VERIFY:"
            f" expected_tvm={len(expected_tvm)} found_tvm={len(found_tvm)}"
            f" expected_fift={len(expected_fift)} found_fift={len(found_fift)}"
            f" missing={len(missing_tvm) + len(missing_fift)} dups={len(dup_keys)} extras={len(extra_keys)}"
        )

        def _print_some(label: str, items: list[str], n: int = 30) -> None:
            if not items:
                return
            head = items[:n]
            tail = len(items) - len(head)
            print(f"{label} (showing {len(head)} of {len(items)}):")
            for k in head:
                print(f"- {k}")
            if tail > 0:
                print(f"... and {tail} more")

        _print_some("Missing TVM", missing_tvm)
        _print_some("Missing Fift", missing_fift)
        _print_some("Duplicate SpecKey", dup_keys)
        _print_some("Extra SpecKey", extra_keys)

        if missing_tvm or missing_fift or dup_keys:
            return 3

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
