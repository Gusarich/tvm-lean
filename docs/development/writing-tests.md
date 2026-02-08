# Writing Tests

Tests are organized per instruction under `Tests/Instr/<Family>/`.
Each file defines one `InstrSuite` and registers it.

## Core types

Defined in `Tests/Harness/Registry.lean`:

- `UnitCase`: direct Lean assertion/behavior checks
- `OracleCase`: Lean vs Fift parity case
- `FuzzSpec`: generator-based case production
- `InstrSuite`: grouped suite by `InstrId`

## Minimal suite skeleton

```lean
import Tests.Harness.Registry

open TvmLean
open Tests

namespace Tests.Instr.Arith.ADD

def suite : InstrSuite where
  id := { name := "ADD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.ADD
```

## Running targeted suites

Filter by instruction id:

```sh
lake exe tvm-lean-tests -- --filter ADD
```

Run only one test mode:

```sh
lake exe tvm-lean-tests -- --unit-only
lake exe tvm-lean-tests -- --oracle-only
lake exe tvm-lean-tests -- --fuzz-only
```

## Coverage expectations

Coverage combines implementation probe status with registered test counts.
Use:

```sh
lake exe tvm-lean-coverage -- --format md --out build/coverage.md
```

Aim for instruction rows that are `impl=ok` with non-zero unit/oracle/fuzz coverage
as applicable.
