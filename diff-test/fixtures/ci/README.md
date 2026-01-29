# CI fixtures (mainnet)

This directory contains a small, curated set of **mainnet** transaction fixtures used for deterministic, offline CI.

- Collected via `diff-test/collector` with `--expected-state` enabled (includes `expected.c4`, `expected.c5`, `expected.c7`).
- These fixtures are intended to be stable and fast to run (kept small on purpose).

Run locally:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

