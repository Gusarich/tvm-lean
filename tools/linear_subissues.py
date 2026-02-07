#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass
from typing import Iterable

import linear_sync as ls


SUB_KEY_RE = re.compile(r"(?m)^[ \t]*SubKey:[ \t]*([^\s]+)[ \t]*$")


@dataclass(frozen=True)
class SubissueSpec:
    ws_label: str  # e.g. "ws/tests"
    title_suffix: str  # e.g. "tests"
    checklist_lines: tuple[str, ...]


TVM_SUBISSUES: tuple[SubissueSpec, ...] = (
    SubissueSpec(
        ws_label="ws/spec-audit",
        title_suffix="spec-audit",
        checklist_lines=(
            "- [ ] Read TON C++ ref from parent issue",
            "- [ ] Confirm exit codes / NaN / edge cases",
            "- [ ] Record discrepancies (comment on parent)",
        ),
    ),
    SubissueSpec(
        ws_label="ws/impl",
        title_suffix="impl",
        checklist_lines=(
            "- [ ] Update `Instr` / `Instr.pretty` if needed",
            "- [ ] Update cp0 decode/encode if applicable",
            "- [ ] Implement semantics in `execInstr`",
            "- [ ] Run `lake build`",
        ),
    ),
    SubissueSpec(
        ws_label="ws/tests",
        title_suffix="tests",
        checklist_lines=(
            "- [ ] Add focused unit/oracle/fuzz cases in `Tests/Instr/<Family>/<Instr>.lean`",
            "- [ ] (Optional) Add encode/decode roundtrip coverage",
            "- [ ] Run `lake exe tvm-lean-tests`",
        ),
    ),
    SubissueSpec(
        ws_label="ws/diff",
        title_suffix="diff",
        checklist_lines=(
            "- [ ] Ensure covered by diff fixtures, or collect/add one",
            "- [ ] Run `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit`",
        ),
    ),
    SubissueSpec(
        ws_label="ws/proof",
        title_suffix="proof",
        checklist_lines=(
            "- [ ] Add/extend WF predicates/lemmas as needed",
            "- [ ] Add proofs (or proof scaffolding) for tricky invariants",
        ),
    ),
)

FIFT_SUBISSUES: tuple[SubissueSpec, ...] = (
    SubissueSpec(
        ws_label="ws/spec-audit",
        title_suffix="spec-audit",
        checklist_lines=(
            "- [ ] Verify alias expansion matches spec",
            "- [ ] Confirm actual instruction behavior if needed",
        ),
    ),
    SubissueSpec(
        ws_label="ws/impl",
        title_suffix="impl",
        checklist_lines=(
            "- [ ] Ensure decoder/pretty-printer/assembler handles alias",
            "- [ ] Run `lake build`",
        ),
    ),
    SubissueSpec(
        ws_label="ws/tests",
        title_suffix="tests",
        checklist_lines=(
            "- [ ] Add focused unit test(s)",
            "- [ ] Run `lake exe tvm-lean-tests`",
        ),
    ),
)


def _extract_sub_key(description: str | None) -> str | None:
    if not description:
        return None
    m = SUB_KEY_RE.search(description)
    return m.group(1) if m else None


def _iter_required_subissues(spec_key: str) -> Iterable[SubissueSpec]:
    if spec_key.startswith("tvm::"):
        return TVM_SUBISSUES
    if spec_key.startswith("fift::"):
        return FIFT_SUBISSUES
    return ()


def _subissue_title(parent_spec_key: str, parent_title: str, *, spec: SubissueSpec) -> str:
    if parent_spec_key.startswith("tvm::"):
        name = parent_spec_key[len("tvm::") :]
        return f"{name}: {spec.title_suffix}"
    if parent_spec_key.startswith("fift::"):
        alias = parent_spec_key[len("fift::") :]
        # Keep it explicit in lists/search.
        return f"Fift alias {alias}: {spec.title_suffix}"
    return f"{parent_title}: {spec.title_suffix}"


def _subissue_description(parent_spec_key: str, *, spec: SubissueSpec) -> str:
    sub_key = f"{parent_spec_key}::{spec.ws_label}"
    lines = [f"SubKey: {sub_key}", "", f"Workstream: {spec.ws_label}", "Parent: see parent issue for spec + TON refs", ""]
    lines.append("Checklist:")
    lines.extend(spec.checklist_lines)
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    ls._load_dotenv(ls.REPO_ROOT / ".env")

    parser = argparse.ArgumentParser(description="Create standard ws/* subissues under each instruction issue in Linear.")
    parser.add_argument("--token", default=os.getenv("LINEAR_API_KEY") or "", help="Linear API key (or set LINEAR_API_KEY).")
    parser.add_argument("--apply", action="store_true", help="Actually create missing subissues (default: dry-run).")
    parser.add_argument("--limit", type=int, default=0, help="Optional cap on number of creates (0 = no cap).")
    parser.add_argument(
        "--only",
        default="",
        help="Optional SpecKey prefix filter (e.g. 'tvm::ADD' or 'fift::HASHEXTAR_SHA256').",
    )
    args = parser.parse_args()

    token = args.token.strip()
    if not token:
        print("Missing Linear API key. Provide --token or set LINEAR_API_KEY.", file=sys.stderr)
        return 2

    label_ids_by_name = ls._fetch_label_ids(token)

    all_issues = ls._fetch_project_issues_all(token)
    children_by_parent: dict[str, list[ls.LinearIssue]] = {}
    for iss in all_issues:
        if iss.parent_id:
            children_by_parent.setdefault(iss.parent_id, []).append(iss)

    creates: list[tuple[str, str, str, list[str]]] = []  # (parent_id, title, description, label_names)
    skipped_parents = 0
    for parent in all_issues:
        spec_key = ls._extract_spec_key(parent.description)
        if not spec_key:
            continue
        if args.only and not spec_key.startswith(args.only):
            continue

        required = list(_iter_required_subissues(spec_key))
        if not required:
            skipped_parents += 1
            continue

        existing_children = children_by_parent.get(parent.id, [])
        existing_subkeys = {k for k in (_extract_sub_key(ch.description) for ch in existing_children) if k}

        parent_label_names = sorted(parent.label_names)
        for spec in required:
            sub_key = f"{spec_key}::{spec.ws_label}"
            if sub_key in existing_subkeys:
                continue

            title = _subissue_title(spec_key, parent.title, spec=spec)
            description = _subissue_description(spec_key, spec=spec)

            label_names = parent_label_names + [spec.ws_label]
            creates.append((parent.id, title, description, label_names))

    if not args.apply:
        print(f"dry-run: would create {len(creates)} subissues (skipped_parents={skipped_parents})")
        for parent_id, title, _desc, labels in creates[:20]:
            print(f"- parent={parent_id} title={title} labels={labels}")
        if len(creates) > 20:
            print(f"... and {len(creates) - 20} more")
        return 0

    cap = args.limit if args.limit > 0 else len(creates)
    created = 0
    for parent_id, title, description, label_names in creates[:cap]:
        label_ids: list[str] = []
        missing: list[str] = []
        for name in label_names:
            lid = label_ids_by_name.get(name)
            if not lid:
                missing.append(name)
            else:
                label_ids.append(lid)
        if missing:
            raise RuntimeError(f"missing Linear labels (create them first): {missing}")

        ls._issue_create(token, title=title, description=description, parent_id=parent_id, label_ids=label_ids)
        created += 1
        if created % 50 == 0:
            print(f"created {created}/{cap}...")

    print(f"created {created} subissues")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
