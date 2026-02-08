# TVM Lean

> ⚠️ **Experimental** — This project is in active development and has not been thoroughly tested. Do not rely on its semantics.

A Lean 4 executable model of the TON Virtual Machine (TVM), designed to match the behavior of the [reference C++ implementation](https://github.com/ton-blockchain/ton). It aims to be both a proof-grade semantics package and a high-confidence reference implementation validated against TON's C++ behavior.

## Motivation

The existing C++ code in the [TON monorepo](https://github.com/ton-blockchain/ton) is a tangled mess of legacy code and obscure C++ patterns. TVM is the heart of TON smart contracts, and billions of dollars potentially depend on it, so ensuring its security is essential. Meanwhile, the [existing TVM specification](https://github.com/ton-blockchain/tvm-specification) is often inconsistent and doesn't always describe the actual semantics accurately.

The original idea was to rewrite the specification for all instructions using AI agents. Early experiments with a few instructions showed promising results, but further thinking and experimentation led to pivoting toward this formal verification project instead.

## Goals

- **Full instruction coverage**: Implement all TVM instructions in pure Lean
- **Differential testing**: Heavy diff testing against the reference C++ implementation to catch mismatches
- **Formal proofs**: Prove important properties for all instructions and core TVM mechanics
- **Better specification**: Improve the TVM specification as a side effect

## Status

🚧 **In active development.** Most of the TVM is implemented, but it has not been properly tested yet. Differential testing against randomly sampled mainnet transactions currently shows ~99% of transactions emulating correctly.

The implementation will become a useful foundation for formal verification once it reaches 100% diff-testing accuracy and each instruction has its own dedicated test suite with carefully validated semantics. Until then, treat the semantics as approximate.

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
