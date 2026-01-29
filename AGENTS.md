# Agent Notes (tvm-lean)

## Purpose

`tvm-lean` is an executable Lean model of the TON Virtual Machine (TVM), built to:

- implement TVM instruction semantics incrementally (toward full coverage)
- validate behavior via unit tests and mainnet diff tests
- later support formal verification/proofs without rewriting the core

Instruction coverage/backlog is tracked in Linear (one issue per TVM instruction + one per Fift alias) and is sourced
from the TVM JSON specification.

## Repo structure

- `TvmLean/Core.lean`: instruction AST (`Instr`), cp0 decode/encode, and execution (`execInstr` / `VmState.step`)
- `TvmLean/Boc.lean`: BOC parsing/serialization (“untrusted input layer”)
- `Tests.lean`: unit tests + encode/decode roundtrip checks
- `TvmLean/DiffTest.lean`, `DiffTestMain.lean`: mainnet diff-test runner for JSON fixtures
- `diff-test/collector/`: TypeScript fixture collector (optional; generates new fixtures)
- `third_party/tvm-specification/`: vendored/pinned TVM spec (used to generate indexes)
- `docs/progress/`: generated instruction indexes/tables
- `tools/`: spec/index generation + Linear sync scripts

Docs entrypoint: `docs/START_HERE.md`.

## External reference repos (local clones)

These repos are expected to be available locally for reference and source-auditing:

- TON monorepo: `/workspace/ton`
- TVM spec repo: `/workspace/tvm-specification`

Use them to:

- inspect the authoritative C++ behavior (TON) when implementing or debugging an opcode
- cross-check the JSON spec generator/source (tvm-specification) when spec metadata looks ambiguous

The `tvm-lean` repo vendors a pinned JSON snapshot of the spec under `third_party/tvm-specification/`; treat the local
`/workspace/tvm-specification` clone as *additional context*, not the source of truth for this repo’s pinned snapshot.

