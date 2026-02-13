# TVM Lean

**A formal executable model of the TON Virtual Machine, written in Lean 4.**

Built to match the behavior of the [reference C++ implementation](https://github.com/ton-blockchain/ton) instruction-for-instruction. The goal is a proof-grade semantics that can serve as both a verified specification and a high-confidence reference implementation.

> ⚠️ **Experimental** — This project is in active development. Do not rely on its semantics until testing is complete.

## Status

All 919 TVM instructions are implemented. The vast majority are pure Lean; cryptography-related instructions link to C/C++ implementations via FFI.

### Test coverage

| Category | Instructions | Status |
|---|--:|:-:|
| Arithmetic | 246 | ✅ Tested |
| Cell | 199 | ✅ Tested |
| Dictionary | 143 | 🚧 |
| Continuation | 98 | ✅ Tested |
| Crypto | 50 | 🚧 |
| Stack | 50 | ✅ Tested |
| Other | 133 | 🚧 |

Tested categories have both hand-crafted differential test cases and a randomized fuzz harness running hundreds of generated cases. Every test compares results directly against the C++ reference implementation, and all pass. Coverage for the remaining categories is in progress.

### Transaction-level validation

Real transactions are pulled from the TON mainnet and re-emulated with both the C++ reference implementation and the Lean implementation. The resulting VM states are compared to ensure they match exactly. This currently passes on 100% of a small-scale sample (thousands of transactions). A larger effort targeting millions of real transactions is in progress.

## Motivation

TVM is the execution engine behind every TON smart contract, with billions of dollars potentially at stake. The C++ implementation in the [TON monorepo](https://github.com/ton-blockchain/ton) is difficult to audit and reason about, and the [existing TVM specification](https://github.com/ton-blockchain/tvm-specification) is often inconsistent with the actual runtime behavior.

A formally verified TVM in Lean changes what's possible. Developers can prove properties about their contracts with mathematical certainty all the way down to the VM — things like "this wallet contract will never send more than the owner authorized", "this DEX's AMM logic preserves the constant product invariant across all execution paths", or "this multisig cannot execute without the required number of signatures, regardless of message ordering".

Without verified VM semantics, any smart contract proof is only as trustworthy as the informal spec it's built on. This project aims to provide that foundation: a precise, machine-checked semantics grounded in what TVM actually does, validated against the C++ implementation at scale, suitable for formal proofs about smart contracts all the way down — and, as a side effect, a better TVM specification than the one that exists today.

## License

MIT. See `LICENSE`.
