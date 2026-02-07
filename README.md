# TVM Lean

> ⚠️ **Experimental** — This project is in active development and has not been thoroughly tested. Do not rely on its semantics.

A Lean 4 implementation of the TON Virtual Machine, designed to match the behavior of the [reference C++ implementation](https://github.com/ton-blockchain/ton).

## Motivation

The existing C++ code in the [TON monorepo](https://github.com/ton-blockchain/ton) is a tangled mess of legacy code and obscure C++ patterns. TVM is the heart of TON smart contracts, and billions of dollars potentially depend on it, so ensuring its security is essential. Meanwhile, the [existing TVM specification](https://github.com/ton-blockchain/tvm-specification) is often inconsistent and doesn't always describe the actual semantics accurately.

The original idea was to rewrite the specification for all instructions using AI agents. Early experiments with a few instructions showed promising results, but further thinking and experimentation led me to pivot toward this formal verification project instead.

## Goals

- **Full instruction coverage**: Implement all TVM instructions in pure Lean
- **Differential testing**: Heavy diff testing against the reference C++ implementation to catch mismatches
- **Formal proofs**: Prove important properties for all instructions and core TVM mechanics
- **Better specification**: Improve the TVM specification as a side effect

## Status

🚧 **In active development.** Most of the TVM is implemented, but it has not been properly tested yet. Differential testing against randomly sampled mainnet transactions currently shows ~99% of transactions emulating correctly.

The implementation will become a useful foundation for formal verification once it reaches 100% diff-testing accuracy and each instruction has its own dedicated test suite with carefully validated semantics. Until then, treat the semantics as approximate.

## Testing

Run the unit suite:

```sh
lake exe tvm-lean-tests
```

The test runner includes an oracle parity pass (`oracle/parity_all_instructions`) that executes every instruction in both:

- Lean VM (`tvm-lean`)
- TON C++ reference VM (via `~/Coding/ton/build/crypto/fift`)

and compares `exit code`, `gas used`, `c4`, `c5`, and full stack results.

Defaults are deterministic and non-random:

- `20` cases per instruction
- `8` code-layout variants per instruction
- `20` stack/input variants per instruction
- enforced minimum `10` cases per instruction

Useful env overrides:

```sh
TVMLEAN_ORACLE_ONLY=ADD TVMLEAN_ORACLE_CASES=20 lake exe tvm-lean-tests
TVMLEAN_ORACLE_LIMIT=50 lake exe tvm-lean-tests
TVMLEAN_ORACLE_RANDOM_CASES=4096 TVMLEAN_ORACLE_SEED=1337 lake exe tvm-lean-tests
TVMLEAN_ORACLE_ENABLED=0 lake exe tvm-lean-tests  # skip oracle parity pass
```

For high-coverage all-instruction parity sweeps (Lean vs Fift `runvmx`), use:

```sh
tools/run_oracle_validate_extensive.sh
```

This runs a multi-seed bounded-exhaustive+randomized matrix and writes logs/results under `oracle/_runs/`.
