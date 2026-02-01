# TVM Lean

> ⚠️ **Work in Progress** — This project is in early development and has not been thoroughly tested. The repo is public primarily to allow running CI jobs without private repository restrictions.

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

🚧 Early development. Check back for updates.
