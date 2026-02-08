# Running Tests

## Fast local gates

```sh
lake build
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
lake exe tvm-lean-tests
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```

## Instruction-focused loop

```sh
lake build TvmLeanSemantics
lake exe tvm-lean-tests -- --filter <InstrId>
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-progress -- --filter <InstrId>
```

## Slower periodic validation

Oracle parity:

```sh
lake exe tvm-lean-tests -- --oracle-only
tools/run_oracle_validate.sh
```

Fuzz sweeps:

```sh
lake exe tvm-lean-tests -- --fuzz-only
```

Extended diff tests:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/curated --strict-exit
```

Coverage review:

```sh
lake exe tvm-lean-coverage -- --format md --out build/coverage.md
```
