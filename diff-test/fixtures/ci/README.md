# CI fixtures (mainnet)

This directory contains a small, curated set of **mainnet** transaction fixtures used for deterministic, offline CI.

- Collected via `diff-test/collector`, with expected state computed by TON C++ (`fift` + `runvmx`) and stored in `expected.exit_code`, `expected.gas_used`, `expected.c4_boc`, `expected.c5_boc`.
- These fixtures are intended to be stable and fast to run (kept small on purpose).
- Precompiled contracts (ConfigParam 45) are intentionally excluded, since the `runvmx` oracle does not support them and `tvm-lean` does not special-case their semantics.

Run locally:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```
