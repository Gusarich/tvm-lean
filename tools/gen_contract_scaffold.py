#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
from pathlib import Path


def to_module_piece(raw: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    if not cleaned:
        cleaned = "Contract"
    parts = [p for p in cleaned.split("_") if p]
    if parts:
        cleaned = "".join(p[:1].upper() + p[1:] for p in parts)
    if cleaned and cleaned[0].isdigit():
        cleaned = f"C{cleaned}"
    return cleaned


def render_program(module_root: str) -> str:
    ns = f"{module_root}.Program"
    return "\n".join(
        [
            "import TvmLean.Model",
            "",
            f"namespace {ns}",
            "",
            "open TvmLean",
            "",
            "-- Replace with your contract instruction sequence.",
            "def program : List Instr :=",
            "  []",
            "",
            "-- Optional assembler bridge when your program is CP0 encodable.",
            "def bytecode : Except Excno Cell :=",
            "  assembleCp0 program",
            "",
            f"end {ns}",
            "",
        ]
    )


def render_spec(module_root: str) -> str:
    ns = f"{module_root}.Spec"
    return "\n".join(
        [
            f"import {module_root}.Program",
            "",
            f"namespace {ns}",
            "",
            "open TvmLean",
            "",
            "-- Replace with contract-specific state observed by the spec.",
            "structure SpecState where",
            "  c4 : Cell",
            "  deriving Repr",
            "",
            "-- Replace with concrete pre/post conditions.",
            "def Pre (_st : SpecState) : Prop := True",
            "def Post (_st0 _st1 : SpecState) : Prop := True",
            "",
            f"end {ns}",
            "",
        ]
    )


def render_proof(module_root: str) -> str:
    ns = f"{module_root}.Proof"
    return "\n".join(
        [
            "import TvmLean.Proof",
            f"import {module_root}.Program",
            f"import {module_root}.Spec",
            "",
            f"namespace {ns}",
            "",
            "open TvmLean",
            "",
            "-- Replace with the contract init state builder.",
            "def initState : VmState :=",
            "  VmState.initial Cell.empty GasLimits.infty",
            "",
            "-- Replace with your execution theorem.",
            "theorem scaffold_smoke : True := by",
            "  trivial",
            "",
            f"end {ns}",
            "",
        ]
    )


def write_if_needed(path: Path, content: str, overwrite: bool) -> None:
    if path.exists() and not overwrite:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate Lean scaffold files for a new contract proof.")
    parser.add_argument("name", help="Contract name (e.g. ToyCounter, WalletV4).")
    parser.add_argument(
        "--out-dir",
        default="Contracts",
        help="Contracts root directory relative to repository root (default: Contracts).",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Overwrite existing files.",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    module_piece = to_module_piece(args.name)
    contract_dir = (repo_root / args.out_dir / module_piece).resolve()
    module_root = f"Contracts.{module_piece}"

    write_if_needed(contract_dir / "Program.lean", render_program(module_root), args.overwrite)
    write_if_needed(contract_dir / "Spec.lean", render_spec(module_root), args.overwrite)
    write_if_needed(contract_dir / "Proof.lean", render_proof(module_root), args.overwrite)

    print(f"generated scaffold in {contract_dir}")
    print(f"modules: {module_root}.Program, {module_root}.Spec, {module_root}.Proof")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
