# Contributing

## Add a new instruction

1. Update instruction surfaces as needed:
   - `TvmLean/Model/Instr/Ast.lean`
   - `TvmLean/Model/Instr/Codepage/Cp0.lean`
   - `TvmLean/Model/Instr/Asm/Cp0.lean`
2. Implement semantics in the correct family file under `TvmLean/Semantics/Exec/`.
3. Add/update the instruction suite under `Tests/Instr/<Family>/<Instr>.lean`.
4. Run oracle and diff validation for regressions.

## Write tests

Use the harness documented in `docs/development/writing-tests.md`.

- `InstrSuite` groups test coverage per `InstrId`.
- Add `UnitCase`, `OracleCase`, and/or `FuzzSpec` depending on behavior and risk.

## Style and conventions

- Keep Model and Semantics free of `@[extern]`.
- Route host-dependent behavior through `Host`.
- Prefer small, instruction-local changes with explicit coverage updates.
- Keep imports minimal and aligned with layer boundaries.

## Pre-PR checklist

```sh
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
lake exe tvm-lean-tests
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```

## PR process

- Keep each PR scoped to one meaningful task.
- Reference the related issue key in the PR title/body.
- Include validation commands run and any known follow-ups.
