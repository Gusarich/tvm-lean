#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
CURATED_DIR = REPO_ROOT / "diff-test" / "fixtures" / "curated"


def unique_dest(path: Path) -> Path:
    if not path.exists():
      return path
    stem = path.stem
    suffix = path.suffix
    i = 2
    while True:
        cand = path.with_name(f"{stem}_{i}{suffix}")
        if not cand.exists():
            return cand
        i += 1


def main() -> int:
    ap = argparse.ArgumentParser(description="Promote a diff-test fixture into curated/ after validation.")
    ap.add_argument("fixture", help="Path to fixture JSON (typically from diff-test/work/)")
    ap.add_argument("--dest-name", default="", help="Optional destination filename")
    ap.add_argument("--skip-validate", action="store_true", help="Skip running tvm-lean-diff-test before copy")
    args = ap.parse_args()

    src = (REPO_ROOT / args.fixture).resolve() if not Path(args.fixture).is_absolute() else Path(args.fixture)
    if not src.exists():
        raise SystemExit(f"fixture not found: {src}")
    if src.suffix.lower() != ".json":
        raise SystemExit(f"fixture must be a .json file: {src}")

    if not args.skip_validate:
        cmd = [
            "lake",
            "exe",
            "tvm-lean-diff-test",
            "--",
            "--case",
            str(src),
            "--strict-exit",
        ]
        p = subprocess.run(cmd, cwd=REPO_ROOT)
        if p.returncode != 0:
            raise SystemExit(f"validation failed for {src} (exit={p.returncode})")

    CURATED_DIR.mkdir(parents=True, exist_ok=True)
    if args.dest_name:
        dest = CURATED_DIR / args.dest_name
    else:
        dest = CURATED_DIR / src.name
    dest = unique_dest(dest)

    shutil.copy2(src, dest)
    print(f"promoted: {src} -> {dest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
