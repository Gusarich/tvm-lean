# tvm-lean

Executable Lean model of a small subset of the TON Virtual Machine (TVM), structured to later support formal verification.

## Status

- Milestone 1: executable VM state + small-step semantics, plus WF predicate scaffolding (proofs are `sorry` for now).
- Milestone 2: cp0 bitcode decoding and a minimal BOC loader (fast-path, untrusted input layer).
- Opcode coverage is intentionally partial; see `docs/progress/instructions.csv`.

## Quickstart

Build:

```sh
lake build
```

Run the built-in “counter” demo (assembles cp0 bitcode in Lean):

```sh
lake exe tvm-lean
```

Run from a BOC containing a *code* cell:

```sh
lake exe tvm-lean -- --boc /path/to/code.boc --c4 41 --fuel 200
```

Run tests:

```sh
lake exe tvm-lean-tests
```

## Notes / limitations

- The BOC parser in `TvmLean/Boc.lean` is a “Milestone 2 fast path” for untrusted input: it verifies header sizes and (if present) CRC32C, supports exotic/special cells + non-zero level masks, and validates hashes/depths when `with_hashes` is present. It still rejects **absent cells** (incomplete BoCs).
- The CLI `--boc` flag expects a *binary* `.boc`. Test fixtures in `fixtures/*.boc.hex` are hex strings (used by `Tests.lean`).
