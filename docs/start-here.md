# tvm-lean: Start Here

`tvm-lean` is an executable Lean model of the TON Virtual Machine (TVM).
It is structured so we can incrementally implement instruction semantics,
validate behavior against TON C++, and later write proofs without rewriting the core.

## Repository layout

- `TvmLean/Model/`: proof-grade pure model (types, state, AST, decode/encode helpers)
- `TvmLean/Semantics/`: execution semantics (`execInstr`, `step`, tracing, run loops)
- `TvmLean/Native/`: native host + extern bindings
- `TvmLean/Validation/`: diff/oracle/canonicalization/reporting helpers
- `Tests/`: instruction-oriented test harness and per-instruction suites
- `Apps/`: CLI entrypoints (`tvm-lean`, `tvm-lean-tests`, `tvm-lean-diff-test`, ...)
- `docs/progress/`: generated spec index and progress tables
- `third_party/tvm-specification/`: pinned vendored TVM spec snapshot

## Quick start

Build core + full project targets:

```sh
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
```

Run the demo executable:

```sh
lake exe tvm-lean
```

Run test harness:

```sh
lake exe tvm-lean-tests
```

Run curated diff-tests (CI fixture set):

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

Generate coverage report:

```sh
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```

## Oracle parity validation

Run the oracle validator for one instruction:

```sh
lake exe tvm-lean-oracle -- --only ADDINT --variants 20 --code-variants 8 --cases 20
```

Run a parallel sweep:

```sh
tools/run_oracle_validate.sh --jobs 12 --variants 20 --code-variants 8 --cases 20
```

## Where to continue

- Architecture details: `docs/architecture/overview.md`
- Implementing instructions: `docs/development/implementing-instructions.md`
- Writing test suites: `docs/development/writing-tests.md`
- Validation workflow: `docs/validation/diff-testing.md`, `docs/validation/oracle.md`
