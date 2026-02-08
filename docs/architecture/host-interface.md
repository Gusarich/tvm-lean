# Host Interface

## Why Host exists

Some TVM operations depend on functionality outside Lean semantics (crypto/hash and
environment interactions). If these were called directly from semantics via externs,
proof-grade code would inherit foreign assumptions everywhere.

`Host` exists to isolate that boundary.

## What Host provides

`TvmLean/Model/Host/Host.lean` defines an abstract interface used by semantics.
Instruction handlers call Host fields instead of calling extern functions directly.

Concrete implementations live outside Model/Semantics:

- `TvmLean.Native.Host.NativeHost`: production/native host
- `TvmLean.Native.Host.StubHost`: deterministic fallback host

## Proof benefit

Because `execInstr`, `step`, and `run` all take `Host` explicitly, proof users can:

- instantiate semantics with a symbolic/axiomatic host,
- reason about host-independent instruction behavior,
- isolate assumptions about external cryptography or environment behavior.

## Engineering benefit

Host separation also improves testing and portability:

- deterministic stub host for tests
- native host only where needed
- no `@[extern]` in `Model` or `Semantics`
