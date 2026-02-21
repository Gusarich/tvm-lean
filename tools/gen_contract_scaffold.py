#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
from pathlib import Path

PROFILES = ("straight", "dict", "flow", "loop")

PROFILE_PROGRAM_HINTS = {
    "dict": [
        "-- Profile: dict (dictionary-backed state updates).",
        "-- Capture key reads/writes and hash updates before instruction encoding.",
        "def dictTouchpoints : List String :=",
        "  []",
        "",
    ],
    "flow": [
        "-- Profile: flow (branch-heavy control flow).",
        "-- Map opcode routing checkpoints before filling in handlers.",
        "def flowCheckpoints : List String :=",
        "  []",
        "",
    ],
    "loop": [
        "-- Profile: loop (iterative execution pattern).",
        "-- Document loop phases and termination guards up-front.",
        "def loopPhases : List String :=",
        "  []",
        "",
    ],
}

PROFILE_SPEC_HINTS = {
    "dict": "-- Dict profile: model dictionary roots and key-level effects in SpecState.",
    "flow": "-- Flow profile: model control predicates and branch outcomes in SpecState.",
    "loop": "-- Loop profile: model loop cursor/fuel and progress obligations in SpecState.",
}

PROFILE_PROOF_HINTS = {
    "dict": [
        "-- Dict profile: prove each dictionary mutation preserves encoding invariants.",
        "def dictProofPlan : List String :=",
        "  []",
        "",
    ],
    "flow": [
        "-- Flow profile: prove branch dispatch chooses the expected handler path.",
        "def flowProofPlan : List String :=",
        "  []",
        "",
    ],
    "loop": [
        "-- Loop profile: prove loop body preserves safety and decreases a progress metric.",
        "def loopProofPlan : List String :=",
        "  []",
        "",
    ],
}


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


def add_bytecode_bridge(lines: list[str]) -> None:
    lines.extend(
        [
            "-- Optional assembler bridge when your program is CP0 encodable.",
            "def bytecode : Except Excno Cell :=",
            "  assembleCp0 program",
            "",
        ]
    )


def render_local_validation_block(program_path: str, spec_path: str, proof_path: str) -> list[str]:
    return [
        "-- Local validation commands (run from repo root):",
        f"--   lake env lean {program_path}",
        f"--   lake env lean {spec_path}",
        f"--   lake env lean {proof_path}",
        "",
    ]


def rel_or_abs(path: Path, repo_root: Path) -> str:
    try:
        return path.relative_to(repo_root).as_posix()
    except ValueError:
        return path.as_posix()


def lint_generated_content(path: Path, namespace: str, content: str, validation_block: list[str]) -> None:
    if "\t" in content:
        raise SystemExit(f"post-check failed: tabs are not allowed in generated file {path}")
    if not content.endswith("\n"):
        raise SystemExit(f"post-check failed: generated file is missing trailing newline: {path}")

    required_markers = [f"namespace {namespace}", f"end {namespace}", validation_block[0]]
    required_markers.extend(line for line in validation_block[1:] if line.startswith("--   lake env lean "))
    for marker in required_markers:
        if marker not in content:
            raise SystemExit(f"post-check failed: missing marker in {path}: {marker}")


def run_post_generation_checks(expected: dict[Path, str], written: set[Path]) -> None:
    for path, expected_content in expected.items():
        if not path.exists():
            raise SystemExit(f"post-check failed: missing generated file {path}")
        if path.stat().st_size == 0:
            raise SystemExit(f"post-check failed: empty generated file {path}")
        if path in written:
            actual_content = path.read_text(encoding="utf-8")
            if actual_content != expected_content:
                raise SystemExit(f"post-check failed: content mismatch after write {path}")


def render_program(module_root: str, profile: str, bytecode_bridge: bool, validation_block: list[str]) -> str:
    ns = f"{module_root}.Program"
    lines = [
        "import TvmLean.Model",
        "",
        f"namespace {ns}",
        "",
        "open TvmLean",
        "",
    ]
    lines.extend(validation_block)
    if profile in PROFILE_PROGRAM_HINTS:
        lines.extend(PROFILE_PROGRAM_HINTS[profile])
    lines.extend(
        [
            "-- Replace with your contract instruction sequence.",
            "def program : List Instr :=",
            "  []",
            "",
        ]
    )
    if bytecode_bridge:
        add_bytecode_bridge(lines)
    else:
        lines.extend(
            [
                "-- Bytecode bridge omitted (enable with --with-bytecode-bridge).",
                "",
            ]
        )
    lines.extend([f"end {ns}", ""])
    return "\n".join(lines)


def render_spec(module_root: str, profile: str, with_invariants: bool, validation_block: list[str]) -> str:
    ns = f"{module_root}.Spec"
    lines = [
        f"import {module_root}.Program",
        "",
        f"namespace {ns}",
        "",
        "open TvmLean",
        "",
    ]
    lines.extend(validation_block)
    hint = PROFILE_SPEC_HINTS.get(profile)
    if hint:
        lines.extend([hint, ""])
    lines.extend(
        [
            "-- Replace with contract-specific state observed by the spec.",
            "structure SpecState where",
            "  c4 : Cell",
            "  deriving Repr",
            "",
            "-- Replace with concrete pre/post conditions.",
            "def Pre (_st : SpecState) : Prop := True",
            "def Post (_st0 _st1 : SpecState) : Prop := True",
            "",
        ]
    )
    if with_invariants:
        lines.extend(
            [
                "-- Optional invariant placeholders.",
                "def Invariant (_st : SpecState) : Prop := True",
                "def PreservesInvariant (st0 st1 : SpecState) : Prop :=",
                "  Invariant st0 -> Invariant st1",
                "",
            ]
        )
    lines.extend([f"end {ns}", ""])
    return "\n".join(lines)


def render_proof(module_root: str, profile: str, with_invariants: bool, validation_block: list[str]) -> str:
    ns = f"{module_root}.Proof"
    lines = [
        "import TvmLean.Proof",
        f"import {module_root}.Program",
        f"import {module_root}.Spec",
        "",
        f"namespace {ns}",
        "",
        "open TvmLean",
        "",
    ]
    lines.extend(validation_block)
    if profile in PROFILE_PROOF_HINTS:
        lines.extend(PROFILE_PROOF_HINTS[profile])
    lines.extend(
        [
            "-- Replace with the contract init state builder.",
            "def initState : VmState :=",
            "  VmState.initial Cell.empty GasLimits.infty",
            "",
            "-- Replace with your execution theorem.",
            "theorem scaffold_smoke : True := by",
            "  trivial",
            "",
        ]
    )
    if with_invariants:
        lines.extend(
            [
                "-- Optional invariant placeholders.",
                f"theorem scaffold_invariant (st : {module_root}.Spec.SpecState) :",
                f"    {module_root}.Spec.Invariant st := by",
                "  trivial",
                "",
                f"theorem scaffold_invariant_step (st0 st1 : {module_root}.Spec.SpecState) :",
                f"    {module_root}.Spec.PreservesInvariant st0 st1 := by",
                "  intro _hInv",
                "  trivial",
                "",
            ]
        )
    lines.extend([f"end {ns}", ""])
    return "\n".join(lines)


def write_if_needed(path: Path, content: str, overwrite: bool) -> bool:
    if path.exists() and not overwrite:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate Lean scaffold files for a new contract proof.")
    parser.add_argument("name", help="Contract name (e.g. ToyCounter, WalletV4).")
    parser.add_argument(
        "--out-dir",
        default="Contracts",
        help="Contracts root directory relative to repository root (default: Contracts).",
    )
    parser.add_argument(
        "--profile",
        "--mode",
        choices=PROFILES,
        default="straight",
        help="Template profile/mode (default: straight).",
    )
    parser.add_argument(
        "--with-invariants",
        action="store_true",
        help="Add invariant placeholders to Spec/Proof skeletons.",
    )
    bytecode_group = parser.add_mutually_exclusive_group()
    bytecode_group.add_argument(
        "--with-bytecode-bridge",
        dest="bytecode_bridge",
        action="store_true",
        default=True,
        help="Include assembleCp0 bytecode bridge in Program (default: enabled).",
    )
    bytecode_group.add_argument(
        "--no-bytecode-bridge",
        dest="bytecode_bridge",
        action="store_false",
        help="Skip bytecode bridge generation in Program.",
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
    program_path = contract_dir / "Program.lean"
    spec_path = contract_dir / "Spec.lean"
    proof_path = contract_dir / "Proof.lean"
    validation_block = render_local_validation_block(
        rel_or_abs(program_path, repo_root),
        rel_or_abs(spec_path, repo_root),
        rel_or_abs(proof_path, repo_root),
    )

    rendered_files: dict[Path, tuple[str, str]] = {
        program_path: (
            render_program(module_root, args.profile, args.bytecode_bridge, validation_block),
            f"{module_root}.Program",
        ),
        spec_path: (
            render_spec(module_root, args.profile, args.with_invariants, validation_block),
            f"{module_root}.Spec",
        ),
        proof_path: (
            render_proof(module_root, args.profile, args.with_invariants, validation_block),
            f"{module_root}.Proof",
        ),
    }
    for path, (content, namespace) in rendered_files.items():
        lint_generated_content(path, namespace, content, validation_block)

    written_paths: set[Path] = set()
    for path, (content, _namespace) in rendered_files.items():
        if write_if_needed(path, content, args.overwrite):
            written_paths.add(path)

    run_post_generation_checks({path: content for path, (content, _ns) in rendered_files.items()}, written_paths)

    print(f"generated scaffold in {contract_dir}")
    print(f"modules: {module_root}.Program, {module_root}.Spec, {module_root}.Proof")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
