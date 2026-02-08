# Implementing Instructions

This project tracks one backlog item per TVM instruction (and one per Fift alias).
Use the generated spec index (`docs/progress/tvm_spec_index.json`) and linked TON
references to implement semantics precisely.

## 1. Locate instruction surfaces

For instruction `FOO`, inspect:

- `TvmLean/Model/Instr/Ast.lean` (constructor + pretty names)
- `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode)
- `TvmLean/Model/Instr/Asm/Cp0.lean` (encode/assembly)
- `TvmLean/Semantics/Exec/<Family>.lean` (runtime semantics)

Useful search:

```sh
rg -n "\\bFOO\\b" TvmLean/Model TvmLean/Semantics
```

## 2. Implement semantics

Typical order:

1. Add/update AST constructor if needed.
2. Wire cp0 decode/encode and keep them symmetric.
3. Implement behavior in the relevant family handler.
4. Ensure unsupported partial behavior throws explicit unimplemented/stub errors.

## 3. Add tests

Add/update per-instruction suite in `Tests/Instr/<Family>/<Instr>.lean`.

A suite can include:

- unit cases (`UnitCase`)
- oracle parity cases (`OracleCase`)
- fuzz specs (`FuzzSpec`)

Register the suite via:

```lean
initialize registerSuite suite
```

See `docs/development/writing-tests.md`.

## 4. Validate locally

```sh
lake build TvmLeanSemantics
lake exe tvm-lean-tests -- --filter <InstrId>
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-progress -- --filter <InstrId>
```

## 5. Full pre-PR sweep

```sh
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
lake exe tvm-lean-tests
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```
