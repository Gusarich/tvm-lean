#!/usr/bin/env python3
from __future__ import annotations

import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Optional


REPO_ROOT = Path(__file__).resolve().parents[1]
SPEC_PATH = REPO_ROOT / "third_party/tvm-specification/tvm-specification.json"
UPSTREAM_PATH = REPO_ROOT / "third_party/tvm-specification/UPSTREAM.json"
OUT_JSON = REPO_ROOT / "docs/progress/tvm_spec_index.json"
OUT_CSV = REPO_ROOT / "docs/progress/tvm_spec_index.csv"


def _load_json(path: Path) -> Any:
    with path.open("rb") as f:
        return json.load(f)


def _optional(dct: dict[str, Any] | None, key: str) -> Any | None:
    if not dct:
        return None
    return dct.get(key)


@dataclass(frozen=True)
class TonImpl:
    commit_hash: str
    file_path: str
    line_number: int
    function_name: str


@dataclass(frozen=True)
class Layout:
    kind: str
    prefix: int
    prefix_str: str
    min: int
    max: int
    checkLen: int
    skipLen: int
    tlb: str
    version: Optional[int]
    args: list[dict[str, Any]]
    exec: str


@dataclass(frozen=True)
class SpecInstructionIndexRow:
    kind: str  # "tvm"
    name: str
    category: str
    sub_category: str
    short: str
    signature_stack_string: Optional[str]
    layout: Layout
    implementation: Optional[TonImpl]


@dataclass(frozen=True)
class SpecFiftAliasIndexRow:
    kind: str  # "fift"
    name: str
    actual_name: str
    actual_category: Optional[str]
    actual_sub_category: Optional[str]


def _parse_instruction(ins: dict[str, Any]) -> SpecInstructionIndexRow:
    desc: dict[str, Any] = ins.get("description") or {}
    sig: dict[str, Any] = ins.get("signature") or {}
    lay: dict[str, Any] = ins.get("layout") or {}

    impl_raw = ins.get("implementation")
    impl = (
        TonImpl(
            commit_hash=str(impl_raw["commit_hash"]),
            file_path=str(impl_raw["file_path"]),
            line_number=int(impl_raw["line_number"]),
            function_name=str(impl_raw["function_name"]),
        )
        if impl_raw
        else None
    )

    layout = Layout(
        kind=str(lay["kind"]),
        prefix=int(lay["prefix"]),
        prefix_str=str(lay["prefix_str"]),
        min=int(lay["min"]),
        max=int(lay["max"]),
        checkLen=int(lay["checkLen"]),
        skipLen=int(lay["skipLen"]),
        tlb=str(lay["tlb"]),
        version=int(lay["version"]) if "version" in lay else None,
        args=list(lay.get("args") or []),
        exec=str(lay.get("exec") or ""),
    )

    return SpecInstructionIndexRow(
        kind="tvm",
        name=str(ins["name"]),
        category=str(ins.get("category") or ""),
        sub_category=str(ins.get("sub_category") or ""),
        short=str(desc.get("short") or ""),
        signature_stack_string=_optional(sig, "stack_string"),
        layout=layout,
        implementation=impl,
    )


def main() -> None:
    if not SPEC_PATH.exists():
        raise SystemExit(f"missing {SPEC_PATH}")
    if not UPSTREAM_PATH.exists():
        raise SystemExit(f"missing {UPSTREAM_PATH}")

    spec = _load_json(SPEC_PATH)
    upstream = _load_json(UPSTREAM_PATH)

    instructions: list[dict[str, Any]] = list(spec["instructions"])
    fift: list[dict[str, Any]] = list(spec.get("fift_instructions") or [])

    idx_by_name: dict[str, SpecInstructionIndexRow] = {}
    rows: list[SpecInstructionIndexRow] = []
    for ins in instructions:
        row = _parse_instruction(ins)
        if row.name in idx_by_name:
            raise SystemExit(f"duplicate instruction name in spec: {row.name}")
        idx_by_name[row.name] = row
        rows.append(row)

    fift_rows: list[SpecFiftAliasIndexRow] = []
    for fa in fift:
        name = str(fa["name"])
        actual = str(fa["actual_name"])
        actual_row = idx_by_name.get(actual)
        fift_rows.append(
            SpecFiftAliasIndexRow(
                kind="fift",
                name=name,
                actual_name=actual,
                actual_category=actual_row.category if actual_row else None,
                actual_sub_category=actual_row.sub_category if actual_row else None,
            )
        )

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "upstream": upstream,
        "spec_version": spec.get("version"),
        "counts": {
            "tvm_instructions": len(rows),
            "fift_instructions": len(fift_rows),
        },
        "tvm_instructions": [asdict(r) for r in rows],
        "fift_instructions": [asdict(r) for r in fift_rows],
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")

    with OUT_CSV.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "kind",
                "name",
                "category",
                "sub_category",
                "prefix_str",
                "layout_kind",
                "checkLen",
                "skipLen",
                "version",
                "ton_commit_hash",
                "ton_file_path",
                "ton_line_number",
                "ton_function_name",
            ]
        )
        for r in rows:
            impl = r.implementation
            w.writerow(
                [
                    r.kind,
                    r.name,
                    r.category,
                    r.sub_category,
                    r.layout.prefix_str,
                    r.layout.kind,
                    r.layout.checkLen,
                    r.layout.skipLen,
                    r.layout.version if r.layout.version is not None else "",
                    impl.commit_hash if impl else "",
                    impl.file_path if impl else "",
                    impl.line_number if impl else "",
                    impl.function_name if impl else "",
                ]
            )
        for fr in fift_rows:
            w.writerow(
                [
                    fr.kind,
                    fr.name,
                    fr.actual_category or "",
                    fr.actual_sub_category or "",
                    "",
                    "",
                    "",
                    "",
                    "",
                    "",
                    "",
                    "",
                    "",
                ]
            )

    print(f"wrote {OUT_JSON}")
    print(f"wrote {OUT_CSV}")


if __name__ == "__main__":
    main()

