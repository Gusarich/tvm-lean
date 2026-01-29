#!/usr/bin/env python3
from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SPEC_INDEX_JSON = REPO_ROOT / "docs/progress/tvm_spec_index.json"
LEGACY_PROGRESS_CSV = REPO_ROOT / "docs/progress/instructions.csv"
OUT_CSV = REPO_ROOT / "docs/progress/instructions_full.csv"


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


def main() -> None:
    if not SPEC_INDEX_JSON.exists():
        raise SystemExit(f"missing {SPEC_INDEX_JSON}; run tools/gen_spec_index.py first")

    idx = _load_json(SPEC_INDEX_JSON)
    tvm: list[dict[str, Any]] = idx["tvm_instructions"]
    fift: list[dict[str, Any]] = idx["fift_instructions"]

    legacy = _load_legacy_progress(LEGACY_PROGRESS_CSV)

    OUT_CSV.parent.mkdir(parents=True, exist_ok=True)
    with OUT_CSV.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["kind", "name", "category", "sub_category", "implemented", "tested", "notes"])

        for ins in tvm:
            name = ins["name"]
            impl, tested = legacy.get(name, (False, False))
            w.writerow(["tvm", name, ins.get("category", ""), ins.get("sub_category", ""), str(impl).lower(), str(tested).lower(), ""])

        for fa in fift:
            w.writerow(
                [
                    "fift",
                    fa["name"],
                    fa.get("actual_category") or "",
                    fa.get("actual_sub_category") or "",
                    "false",
                    "false",
                    f"alias of {fa['actual_name']}",
                ]
            )

    print(f"wrote {OUT_CSV}")


if __name__ == "__main__":
    main()

