# TVM Lean

`tvm-lean` is an executable Lean model of the TON Virtual Machine (TVM). It aims to be both a proof-grade semantics package and a high-confidence reference implementation validated against TON's C++ behavior.

## Architecture

### Model

`TvmLean/Model/` contains the pure VM model: value/cell/slice/builder types, VM state, instruction IDs/AST, and cp0 decode/encode helpers. This layer is designed for proofs and has no FFI.

### Semantics

`TvmLean/Semantics/` contains instruction execution semantics (`execInstr`), step/run logic, and tracing infrastructure. Semantics is parameterized by `Host`.

### Native

`TvmLean/Native/` provides concrete host implementations and all external bindings (`@[extern]`) in one isolated layer.

### Validation

`TvmLean/Validation/` provides diff testing, oracle parity checking, canonicalization helpers, and coverage reporting.

## Quick Start

Build all project libraries:

```sh
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
```

Run tests:

```sh
lake exe tvm-lean-tests
```

Run curated diff tests:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

Generate coverage report:

```sh
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```

## Documentation

- Getting started: `docs/start-here.md`
- Architecture: `docs/architecture/overview.md`
- Instruction implementation workflow: `docs/development/implementing-instructions.md`
- Test writing/running: `docs/development/writing-tests.md`, `docs/development/running-tests.md`
- Validation pipelines: `docs/validation/diff-testing.md`, `docs/validation/oracle.md`

## License

MIT. See `LICENSE`.
