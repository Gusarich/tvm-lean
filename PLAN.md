# `tvm-lean` Full Refactoring Plan

This document describes every piece of the repository restructuring. It is meant to be
read top to bottom and executed roughly in the order written, but it is not phased —
it is one continuous pass that transforms the repository from its current experimental
state to its final clean architecture.

Writing actual test cases (oracle, fuzz, unit content) is explicitly out of scope.
This plan delivers the structure, harnesses, and infrastructure that test cases will
live in. Coverage maxxing comes after.

---

## 0. What This Refactor Is And Why It Matters

The repository was built fast with changing plans. The architecture that resulted
is functional but structurally confused: a god file that everything depends on,
testing infrastructure mixed into the core library, FFI declarations baked into
the proof-grade code, six entrypoints scattered at root, scratch fixtures committed
alongside canonical ones, and a test suite that has volume but no systematic
per-instruction coverage or oracle parity.

The project has now settled on its goals:

1. A formally verifiable TVM model that external Lean projects can import for
   smart contract proofs and TVM safety proofs.
2. A rigorously tested reference implementation validated against C++ TON to the
   highest standard achievable.
3. An open-source project that a newcomer can navigate, understand, and trust.

The current structure cannot serve these goals. The refactor makes the structure
match the goals.

The single most important structural property of the end state is:
**the proof-grade core (Model + Semantics) contains no FFI, no IO, no test
infrastructure, no validation code, and has minimal, explicit internal dependencies.**

Everything else — clean root, per-instruction tests, fixture hygiene — flows from
making that property real and maintaining it.

---

## 1. Kill `TvmLean/Core/Prelude.lean`

### What it is now

`Prelude.lean` contains: `Excno`, `Value`, `IntVal`, cell/slice/builder types and
helpers, continuation types (`Continuation`, `OrdCregs`, `OrdCdata`), `VmState` and
register layout, `GasLimits` and cost constants, stack type and typed-pop helpers in
the VM monad, the full `Instr` AST with all sub-enums, cp0 decode/encode and assembler
helpers, and `@[extern]` FFI declarations for crypto and hashing.

### Why it must die

Every module in the project transitively depends on this file. That means:

- It is impossible to reason about cells without depending on gas constants.
- It is impossible to reason about the instruction AST without depending on FFI declarations.
- Importing the value model forces importing crypto externs.
- Any proof about any part of TVM must axiomatize everything in Prelude, including
  the foreign function interface.

For a proof-grade library this is disqualifying. Module boundaries must reflect logical
dependency boundaries so that proofs can target specific pieces of the model.

### What replaces it

The contents of Prelude are distributed across focused modules under `TvmLean/Model/`:

```
TvmLean/Model/
  Basics/
    Bytes.lean            -- ByteArray helpers, hex, base64, bit operations
    Nat.lean              -- small Nat utility lemmas
    Result.lean           -- Result/Either helpers, no VM coupling
  Error/
    Excno.lean            -- Excno enum
    VmError.lean          -- structured VM error type
  Value/
    IntVal.lean           -- integer representation
    Value.lean            -- Value sum type
  Cell/
    Bitstring.lean        -- bitstring type and operations
    Cell.lean             -- Cell type
    Slice.lean            -- Slice type and navigation
    Builder.lean          -- Builder type and construction
    Primitives.lean       -- pure operations on cells/slices/builders
  Cont/
    Cregs.lean            -- control register types
    Cdata.lean            -- continuation data record
    Continuation.lean     -- continuation variant type
  Gas/
    Types.lean            -- GasLimits type
    Constants.lean        -- cost constants
  Stack/
    Stack.lean            -- pure stack type, no monadic helpers
  State/
    Registers.lean        -- register layout, c0–c7 shapes
    VmState.lean          -- VmState record
  Instr/
    Id.lean               -- InstrId type, canonical names
    Ast.lean              -- Instr and all sub-enums
    Codepage/
      Cp0.lean            -- cp0 decode and encode
    Asm/
      Cp0.lean            -- assembler helpers
  Host/
    Host.lean             -- abstract host interface (structure with crypto/env fields)
```

Each module imports only what it logically requires. The dependency graph is:

- `Basics.*` → nothing
- `Error.*` → `Basics`
- `Value.*` → `Basics`
- `Cell.*` → `Basics`
- `Gas.*` → `Basics`
- `Stack.Stack` → `Value`
- `Cont.*` → `Value`, `Cell`, `Stack`
- `State.VmState` → `Value`, `Cell`, `Cont`, `Gas`, `Stack`
- `Instr.Ast` → `Value`, `Cell` (only if instruction immediates reference them)
- `Instr.Codepage.Cp0` → `Instr.Ast`, `Cell.Slice`
- `Instr.Asm.Cp0` → `Instr.Ast`, `Cell.Builder`
- `Host.Host` → `Value`, `Cell` (defines the abstract interface contract)

**Hard rule: nothing under `Model/` imports anything outside `Model/`.**

`TvmLean/Model.lean` re-exports all of these for convenience, so code that doesn't
care about fine-grained imports can still write `import TvmLean.Model`.

There is no `Prelude.lean` left. Not as a compat wrapper, not as a reexport. It is
gone. Every file that previously imported `TvmLean.Core.Prelude` must be updated to
import the specific modules it needs, or import `TvmLean.Model`.

### How to do it

Go through `Prelude.lean` top to bottom. For each logical block:

1. Create the target module file under `Model/`.
2. Move the definitions there.
3. Add the minimal necessary imports at the top of the new file.
4. Build. Fix any import errors in files that depended on Prelude.
5. Repeat for the next block.

The order matters because of internal dependencies. Do it in this sequence:

1. `Basics/*` (no deps, nothing can break)
2. `Error/Excno.lean`
3. `Value/IntVal.lean`, `Value/Value.lean`
4. `Cell/Bitstring.lean`, `Cell/Cell.lean`, `Cell/Slice.lean`, `Cell/Builder.lean`, `Cell/Primitives.lean`
5. `Gas/Types.lean`, `Gas/Constants.lean`
6. `Stack/Stack.lean`
7. `Cont/Cregs.lean`, `Cont/Cdata.lean`, `Cont/Continuation.lean`
8. `State/Registers.lean`, `State/VmState.lean`
9. `Instr/Id.lean`, `Instr/Ast.lean`
10. `Instr/Codepage/Cp0.lean`, `Instr/Asm/Cp0.lean`
11. `Host/Host.lean`

At each step, the rest of the codebase can still import Prelude because Prelude
still exists and still contains the remaining un-extracted definitions. Once everything
is extracted, Prelude is empty and can be deleted.

The FFI `@[extern]` declarations do NOT go into Model. They go into
`TvmLean/Native/Extern/` later. During extraction, temporarily leave them in Prelude
until the Host abstraction is in place, then move them as part of the Host introduction
(section 3 below).

---

## 2. Restructure `TvmLean/Core/Exec/` → `TvmLean/Semantics/`

### What it is now

`TvmLean/Core/Exec/` contains per-family execution handlers (Arith, Stack, Cell, etc.)
and `TvmLean/Core/Exec.lean` contains the top-level `execInstr` dispatcher.
`TvmLean/Core/Step.lean` contains `VmState.step`, the main state-transition function,
plus tracing infrastructure.

These all live under `TvmLean/Core/` alongside the model types, making "Core" mean
"everything."

### Why it moves

The execution semantics are logically distinct from the data model. Someone proving
a property about cell encoding does not need to import the step function. Someone
proving a property about the instruction AST does not need to import arithmetic
handlers.

More importantly, the execution semantics must be parameterized over `Host` (section 3),
which means they depend on `Model.Host.Host`. The model itself must not depend on
execution semantics. Making them separate directories/libraries enforces this.

### What replaces it

```
TvmLean/Semantics/
  VM/
    Monad.lean            -- VM monad definition
    Ops/
      Stack.lean          -- typed pop, push, peek (currently in Prelude's stack helpers)
      Gas.lean            -- gas charging helpers
      Cells.lean          -- cell/slice/builder operations in the monad
      Cont.lean           -- continuation manipulation in the monad
      State.lean          -- state access and mutation helpers
  Exec/
    Dispatch.lean         -- execInstr : Host → Instr → VM Unit (the main dispatcher)
    Common.lean           -- cross-family shared helpers
    Arith/...             -- all current Exec/Arith files, updated imports
    Stack/...
    Cell/...
    CellOp/...
    Flow/...
    Cont/...
    Exception/...
    Dict/...
    Tuple/...
    TonEnv/...
    Msg/...
    Crypto/...
    Debug/...
    Misc/...
  Step/
    Step.lean             -- step : Host → VmState → VM VmState
    Run.lean              -- run with fuel
    Trace.lean            -- TraceEntry, stepTrace, runTrace
```

Note the new `VM/Ops/` directory. Currently the VM monad helpers (typed stack pops,
gas charging, etc.) live in Prelude alongside the pure types. They belong in Semantics
because they operate within the VM monad — they are execution infrastructure, not
model definitions. During the Prelude split (section 1), the pure stack TYPE goes to
`Model/Stack/Stack.lean`, but the monadic stack OPERATIONS go to `Semantics/VM/Ops/Stack.lean`.

### How to do it

1. Create the `TvmLean/Semantics/` directory structure.
2. Move `TvmLean/Core/Exec/*.lean` files into `TvmLean/Semantics/Exec/` preserving
   the family subdirectory structure.
3. Move `TvmLean/Core/Step.lean` content into `TvmLean/Semantics/Step/Step.lean`,
   splitting tracing into `Trace.lean` and run-with-fuel into `Run.lean`.
4. Extract monadic helpers from Prelude (or wherever they landed during section 1)
   into `TvmLean/Semantics/VM/Ops/*.lean`.
5. Create `TvmLean/Semantics/VM/Monad.lean` with the VM monad definition (currently
   this is probably also in Prelude or implicitly defined alongside the state).
6. Update all imports across the codebase.
7. Delete `TvmLean/Core/Exec/`, `TvmLean/Core/Exec.lean`, `TvmLean/Core/Step.lean`.
8. At this point `TvmLean/Core/` should be empty or nearly empty. Delete it.

---

## 3. Introduce The Host Abstraction And Isolate FFI

### Why this matters

Currently, `@[extern]` declarations for crypto and hashing live in Prelude. Every
module that imports Prelude (which is everything) transitively depends on foreign
code. This means:

- Every proof must axiomatize the behavior of C functions.
- Building the proof-grade library requires linking C objects.
- There is no way to test semantics with a deterministic stub host.

This is the most important architectural change for proof-friendliness.

### What changes

**`TvmLean/Model/Host/Host.lean`** defines an abstract interface:

```lean
structure Host where
  sha256 : ByteArray → ByteArray
  ed25519Verify : ByteArray → ByteArray → ByteArray → Bool
  -- ... every crypto/env operation that currently uses @[extern]
```

This is a plain Lean structure. No FFI. No `@[extern]`. Lives in Model.

**`TvmLean/Semantics/`** is parameterized over Host:

- `execInstr` becomes `execInstr (host : Host) (instr : Instr) : VM Unit`
- `step` becomes `step (host : Host) : VM VmState`
- All crypto family handlers receive `host` and call `host.sha256`, `host.ed25519Verify`, etc.
  instead of calling extern functions directly.
- Non-crypto families can ignore `host` — they just pass it through.

**`TvmLean/Native/Extern/Crypto.lean`** contains the `@[extern]` declarations that
currently live in Prelude:

```lean
@[extern "tvmlean_ed25519_verify"]
opaque ed25519VerifyNative : ByteArray → ByteArray → ByteArray → Bool
-- etc.
```

**`TvmLean/Native/Host/NativeHost.lean`** builds the concrete host:

```lean
def nativeHost : Host where
  sha256 := sha256Native
  ed25519Verify := ed25519VerifyNative
  -- etc.
```

**`TvmLean/Native/Host/StubHost.lean`** builds a deterministic stub for builds
without native dependencies and for certain test scenarios:

```lean
def stubHost : Host where
  sha256 := fun _ => ByteArray.mkEmpty 32  -- or whatever deterministic behavior
  ed25519Verify := fun _ _ _ => false
  -- etc.
```

### How to do it

1. Define `Host` structure in `Model/Host/Host.lean`.
2. Create `Native/Extern/Crypto.lean` and `Native/Extern/Hash.lean`, move all
   `@[extern]` declarations there from wherever they currently live.
3. Create `NativeHost.lean` wiring externs to Host fields.
4. Create `StubHost.lean`.
5. Update all crypto execution handlers in `Semantics/Exec/Crypto/` to take `host`
   parameter and call host methods instead of extern functions.
6. Thread `host` through the dispatch chain: `execInstr` → family dispatchers → handlers.
   For non-crypto families, `host` is just passed through untouched.
7. Thread `host` through `step` and `run`.
8. Update all call sites in Apps, Tests, Validation to pass `nativeHost`.
9. Verify: `TvmLean/Model/` and `TvmLean/Semantics/` now contain zero `@[extern]`
   declarations and zero imports from `TvmLean/Native/`.

This is the widest-reaching change because it touches the signature of `execInstr`,
`step`, and every caller. But it is mechanical — add a parameter, pass it through.
The actual logic of every handler stays identical.

---

## 4. Move Validation Code Out Of `TvmLean/`'s Core Namespace

### What it is now

`TvmLean/DiffTest.lean`, `TvmLean/OracleValidate.lean`, and `TvmLean/CellDiff.lean`
live inside `TvmLean/` alongside the VM model. This means anyone importing `TvmLean`
as a library gets diff-test schemas, oracle harness code, and cell comparison debugging
utilities as part of the package.

### Why it moves

Validation infrastructure is not part of the VM model. It is tooling for checking
the model against a reference. A proof user should never see it. An external project
depending on `TvmLean` should not have these modules in scope.

### What replaces it

```
TvmLean/Validation/
  Canon/
    Value.lean            -- canonical value representation for comparison
    Cell.lean             -- canonical cell comparison (from CellDiff.lean)
    Result.lean           -- canonical execution result type
  Diff/
    Schema.lean           -- fixture JSON schema (StackInit, Expected, TestCase)
    Runner.lean           -- fixture execution and comparison logic
    Report.lean           -- diff-test result and report types
  Oracle/
    Cases.lean            -- OracleCase definition
    Runner.lean           -- run Lean + fift, compare canonical results
    Report.lean           -- oracle comparison reporting
  Coverage/
    InstrStatus.lean      -- per-instruction implementation and test status types
    Report.lean           -- coverage aggregation and report generation
```

### How to do it

1. Create `TvmLean/Validation/` directory structure.
2. Move `DiffTest.lean` contents into `Validation/Diff/Schema.lean` and
   `Validation/Diff/Runner.lean`, splitting schema definitions from execution logic.
3. Move `OracleValidate.lean` contents into `Validation/Oracle/*`.
4. Move `CellDiff.lean` into `Validation/Canon/Cell.lean`.
5. Update imports in Apps and anywhere else that used these modules.
6. Delete the old files. No compat wrappers.

The `Canon/` subdirectory is new and important. Canonical forms for comparison are
used by both diff testing and oracle testing. Having a shared canonical representation
avoids divergence between the two validation approaches.

`Coverage/` is also new. This is where the per-instruction status aggregation lives —
the code that answers "is this instruction implemented, stubbed, or missing? Does it
have unit tests, oracle tests, fuzz tests?" This module reads from the test registry
and from execution probes.

---

## 5. Create `TvmLean/Spec/Index.lean`

### Why it exists

The vendored TVM specification snapshot in `third_party/tvm-specification/` is the
canonical list of all TVM instructions. The repo already has `tools/gen_spec_index.py`
that generates compact index files from it. But there is currently no Lean-native
representation of the spec index.

For per-instruction test coverage to work, there must be a Lean-accessible list of all
instruction IDs. Tests register against these IDs. Coverage tools iterate over them.
Progress reporting compares "what the spec says exists" against "what we have."

### What it is

`TvmLean/Spec/Index.lean` is a generated file containing:

- `InstrId` — an inductive type or string-wrapper representing canonical instruction
  identifiers matching the spec snapshot
- `allInstrIds : Array InstrId` — the complete list
- Whatever metadata per instruction is useful (mnemonic, family, etc.)

This file is generated by extending `tools/gen_spec_index.py` to emit Lean in addition
to JSON/CSV. It should be regenerated whenever the vendored spec snapshot is updated.

### How to do it

1. Extend `tools/gen_spec_index.py` to output `TvmLean/Spec/Index.lean`.
2. Decide on `InstrId` representation. Options:
   - String wrapper (simplest, least type-safe)
   - Inductive with one constructor per instruction (most type-safe, largest generated file)
   - Recommendation: start with string wrapper, upgrade later if needed
3. Generate the file.
4. Ensure `TvmLean/Spec/Index.lean` is importable by both Model and Tests code.
   It depends only on `Model.Basics` at most.

---

## 6. Set Up The `TvmLean/Boc/` Module

### What it is now

BOC (Bag of Cells) serialization already exists and is re-exported by `TvmLean.lean`.

### What changes

Ensure `Boc/` depends only on `Model/Cell/` and `Model/Basics/`. It should not import
anything from Semantics, Native, or Validation. If it currently imports Prelude, update
those imports to point at the specific Model modules.

No structural change to the BOC code itself — just import cleanup.

---

## 7. Delete All Existing Tests And Build The New Test Skeleton

### Why delete everything

The existing ~940 test files were written during exploration without systematic thinking
about what cases each instruction needs. They are organized by domain (Arithmetic, Cell,
etc.) rather than by instruction, making coverage tracking impossible. They do not include
oracle parity tests or randomized tests. They use a registry model that doesn't support
per-instruction coverage queries.

Keeping them would mean either maintaining two test systems in parallel (the old domain
tests and the new per-instruction suites) or migrating them piecemeal into the new
structure. Both options are worse than starting clean, because:

- The old tests are not trusted — they were written without systematic coverage thinking.
- Migration labor produces no new coverage, only reformatted old coverage.
- The new structure is fundamentally different (per-instruction, with oracle and fuzz
  slots) and the old tests don't map cleanly onto it.

### What replaces it

```
Tests/
  Harness/
    Registry.lean         -- InstrSuite type, global registry, registerSuite
    Runner.lean           -- suite execution: runs unit, oracle, fuzz
    OracleHarness.lean    -- Lean vs fift execution and canonical comparison
    FuzzHarness.lean      -- seeded random generation, execution, comparison
    Coverage.lean         -- per-instruction status aggregation
    Cli.lean              -- CLI argument parsing for test executable
  Instr/
    Arith/
      ADD.lean
      SUB.lean
      MUL.lean
      DIV.lean
      DIVMOD.lean
      ...                 -- one file per instruction, grouped by family
    Stack/
      PUSH.lean
      POP.lean
      XCHG.lean
      ...
    Cell/
      NEWC.lean
      ENDC.lean
      STI.lean
      LDI.lean
      ...
    Flow/
      CALL.lean
      JMPX.lean
      RET.lean
      IFELSE.lean
      WHILE.lean
      ...
    Cont/
      ...
    Dict/
      ...
    Tuple/
      ...
    TonEnv/
      ...
    Crypto/
      ...
    Exception/
      ...
    Msg/
      ...
    Debug/
      ...
    Misc/
      ...
  All.lean                -- generated, imports every Tests.Instr.*.* file
```

### The Harness

**`Registry.lean`** defines the core types:

```lean
structure UnitCase where
  name : String
  run : IO Unit           -- or ExceptT, whatever convention is chosen

structure OracleCase where
  name : String
  instr : InstrId
  program : ...           -- assembled code or raw cell
  initStack : ...
  initCregs : ...         -- relevant control registers
  initC7 : ...            -- environment tuple
  gasLimits : ...
  -- no expected output: the oracle IS the expectation

structure FuzzSpec where
  seed : UInt64
  count : Nat
  gen : StdGen → (OracleCase × StdGen)
  -- deterministic, seeded, reproducible

structure InstrSuite where
  id : InstrId
  unit : Array UnitCase
  oracle : Array OracleCase
  fuzz : Array FuzzSpec
```

And a global registry:

```lean
initialize instrSuiteRegistry : IO.Ref (Array InstrSuite) ← IO.mkRef #[]

def registerSuite (suite : InstrSuite) : IO Unit :=
  instrSuiteRegistry.get >>= fun arr => instrSuiteRegistry.set (arr.push suite)
```

**`Runner.lean`** iterates registered suites and runs each kind:

- Unit cases: run directly, report pass/fail.
- Oracle cases: run through `OracleHarness`, compare canonical results.
- Fuzz specs: generate `count` cases from `seed`, run each through `OracleHarness`.

**`OracleHarness.lean`** is the critical piece. It:

1. Takes an `OracleCase`.
2. Assembles and runs it in the Lean VM with `nativeHost`.
3. Serializes the same scenario for `fift runvmx` and runs it.
4. Canonicalizes both results into `Canon.Result`.
5. Compares and produces a structured diff on mismatch.

The details of serialization and fift invocation build on the existing oracle
infrastructure. The key difference is that this is now a library function callable
by the test runner, not a standalone executable.

**`FuzzHarness.lean`** wraps `OracleHarness` with generation:

1. Takes a `FuzzSpec`.
2. Initializes generator from seed.
3. Generates `count` cases.
4. Runs each through `OracleHarness`.
5. On failure: dumps reproducible artifact (instruction ID, seed, iteration index,
   serialized case, both results, diff).

**`Coverage.lean`** answers the questions:

- For each `InstrId` in the spec index: is it implemented (ok / stub / missing)?
- How many unit / oracle / fuzz cases does it have?
- What instructions have zero coverage?

Implementation status comes from execution probes (not manual tables). Run a minimal
program containing the instruction, observe the result:
- Runs successfully → implemented
- Throws `VmError.unimplemented` → stub
- Throws `invOpcode` → not decoded
- Other failure → broken

### Per-instruction file skeleton

Each `Tests/Instr/<Family>/<INSTR>.lean` looks like:

```lean
import Tests.Harness.Registry
import TvmLean.Spec.Index

namespace Tests.Instr.<Family>.<INSTR>

def suite : InstrSuite where
  id := InstrId.mk "<INSTR>"           -- or however InstrId works
  unit := #[]                           -- to be filled
  oracle := #[]                         -- to be filled
  fuzz := #[]                           -- to be filled

initialize registerSuite suite

end Tests.Instr.<Family>.<INSTR>
```

These are empty skeletons. The point of this refactor is to create every skeleton
for every instruction in the spec index, so that the coverage tool can immediately
show the full gap. Filling them in is the next project.

### How `All.lean` is generated

Extend `tools/gen_test_scaffold.py` (or write a new script) that:

1. Reads the spec index.
2. For each instruction, ensures `Tests/Instr/<Family>/<INSTR>.lean` exists.
   If not, creates the skeleton.
3. Generates `Tests/All.lean` importing every instruction file.

This is the same pattern as the current scaffold script but targeting the new structure.

### What gets deleted

- The entire existing `Tests/` directory.
- `Tests.lean` at root (replaced by `Apps/Tests.lean`).
- `Tests/Registry.lean`, `Tests/Util.lean`, `Tests/All.lean` — all replaced by the
  new Harness modules.
- Every `Tests/Arithmetic/*.lean`, `Tests/Cell/*.lean`, etc. — all of them, gone.
- `Tests/Boc.lean`, `Tests/Counter.lean`, `Tests/OracleParity.lean` — integration
  tests that can be recreated in the new structure if needed.

---

## 8. Make Stubs Loud

### What it is now

Some instructions are "implemented" in the dispatch table but don't actually do
anything meaningful — they silently succeed or are no-ops. This is invisible to
testing and progress tooling.

### Why it matters

Silent stubs are lies. They make coverage look better than it is. A diff test can
pass because a stub happens to not affect the final state in that particular scenario.
Per-instruction oracle testing will catch them eventually, but the progress tooling
should catch them immediately.

### What changes

Add a dedicated error variant:

```lean
-- in Model/Error/VmError.lean
| unimplemented (id : InstrId) (msg : String)
```

Add a helper in Semantics:

```lean
def unimplementedInstr (id : InstrId) : VM α :=
  throw (.unimplemented id "not yet implemented")
```

Go through every instruction handler. Any that is currently a stub — does nothing,
returns unit, pushes a dummy value — replace with `unimplementedInstr`. This is
a judgment call per instruction, but the principle is: if the handler does not
faithfully implement the TVM specification's semantics for that instruction, it
should throw `unimplemented`, not silently pretend to work.

The coverage tool in `Tests/Harness/Coverage.lean` detects `unimplemented` distinctly
from `invOpcode`, so the progress report shows three states:

- **ok**: instruction runs and produces results
- **stub**: instruction is decoded and dispatched but throws `unimplemented`
- **missing**: instruction is not decoded (`invOpcode`)

---

## 9. Move All Entrypoints Into `Apps/`

### What it is now

The root contains: `Main.lean`, `DiffTestMain.lean`, `ActionsDebugMain.lean`,
`TraceInspectMain.lean`, `ProgressMain.lean`, `PrecompiledSnapshotMain.lean`,
`OracleValidateMain.lean`, and `Tests.lean`.

### Why they move

Six Main files at root is confusing for newcomers and clutters the project's
top-level story. These are thin CLI wrappers — they parse args and call library
functions. They should be clearly separated from the library code.

### What replaces it

```
Apps/
  Demo.lean               -- was Main.lean
  Tests.lean              -- test suite runner
  DiffTest.lean           -- diff-test runner
  Oracle.lean             -- oracle validation runner
  Progress.lean           -- instruction implementation probe
  Coverage.lean           -- coverage report generator (new)
  TraceInspect.lean       -- trace stop/dump utility
  PrecompiledSnapshot.lean
  ActionsDebug.lean       -- action-list mismatch debugging
```

Each is a `lean_exe` target in `lakefile.lean`:

```lean
lean_exe «tvm-lean»             where root := `Apps.Demo
lean_exe «tvm-lean-tests»      where root := `Apps.Tests
lean_exe «tvm-lean-diff-test»  where root := `Apps.DiffTest
lean_exe «tvm-lean-oracle»     where root := `Apps.Oracle
lean_exe «tvm-lean-progress»   where root := `Apps.Progress
lean_exe «tvm-lean-coverage»   where root := `Apps.Coverage
-- etc.
```

Executable names stay the same so existing scripts and CI don't break.

### What gets deleted

All `*Main.lean` and `Tests.lean` at root. Gone.

---

## 10. Configure Lake Libraries And Package Defaults

### Why multiple libraries

A single `TvmLean` library forces anyone who depends on the package to build
everything, including native code, validation infrastructure, and tests. Splitting
into libraries lets downstream users (proof projects) build only what they need
and avoids requiring C toolchain setup for pure proof work.

### Target structure

```lean
lean_lib TvmLeanModel where
  roots := #[`TvmLean.Model, `TvmLean.Boc, `TvmLean.Spec]

lean_lib TvmLeanSemantics where
  roots := #[`TvmLean.Semantics]

lean_lib TvmLeanNative where
  roots := #[`TvmLean.Native]
  -- moreLinkArgs, extraDepTargets for C objects

lean_lib TvmLeanValidation where
  roots := #[`TvmLean.Validation]

lean_lib TvmLeanTests where
  srcDir := "."
  roots := #[`Tests]
```

Default targets:

```lean
package «tvm-lean» where
  defaultTargets := #[`TvmLeanModel, `TvmLeanSemantics]
```

This means `lake build` from a downstream proof project builds only the proof-grade
code. CI in this repo builds everything explicitly.

### Dependency enforcement

Lake library boundaries enforce the import rules:

- `TvmLeanModel` has no lean library deps (only Lean stdlib/Mathlib if needed).
- `TvmLeanSemantics` depends on `TvmLeanModel`.
- `TvmLeanNative` depends on `TvmLeanModel` (not Semantics — it just provides Host impl).
- `TvmLeanValidation` depends on `TvmLeanSemantics` and `TvmLeanNative`.
- `TvmLeanTests` depends on `TvmLeanValidation` (which transitively gives it everything).

If someone in Model tries to import something from Semantics, Lake will error.
This is the structural guarantee.

---

## 11. Clean Up `diff-test/`

### What it is now

Contains `fixtures_fift_tmp` through `fixtures_fift_tmp_v5`, `fixtures_fift_focus`,
`fixtures/ci/`, `focus_report.json`, and the collector TypeScript project. The tmp
directories are iteration residue from debugging. Nobody knows which are canonical.

### What replaces it

```
diff-test/
  collector/
    src/
      collect.ts
      sweep.ts
      fift_oracle.ts
      gas.ts
    package.json
    tsconfig.json
  fixtures/
    ci/                   -- tracked, deterministic, runs every PR (keep existing)
    smoke/                -- tracked, tiny, fast sanity checks
    curated/              -- tracked, growing set of promoted fixtures
  work/                   -- gitignored, all scratch and experimental fixtures
  scripts/
    pretty_trace.py       -- moved from diff-test/ root
  reports/                -- gitignored, run output
```

### What gets deleted

- `diff-test/fixtures_fift_tmp/`
- `diff-test/fixtures_fift_tmp_v2/`
- `diff-test/fixtures_fift_tmp_v3/` (including `batch/`)
- `diff-test/fixtures_fift_tmp_v4/`
- `diff-test/fixtures_fift_tmp_v5/`
- `diff-test/fixtures_fift_focus/`
- `diff-test/focus_report.json`

If any fixtures in the tmp directories are genuinely valuable, move them to
`fixtures/curated/` before deleting. But default to deleting — they can always be
regenerated from chain data.

### Fixture promotion workflow

Add `tools/promote_fixture.py` that:

1. Takes a fixture file from `diff-test/work/`.
2. Validates it runs correctly.
3. Copies it to `diff-test/fixtures/curated/` with a consistent naming convention.
4. Optionally updates an index file.

This replaces the pattern of creating new `tmp_v*` directories.

---

## 12. Clean Up `oracle/`

### What it is now

Contains tracked smoke run snapshots under `oracle/_runs/_smoke_*` and fift scripts.

### What replaces it

```
oracle/
  fif/                    -- .fif scripts
    ton_oracle_runvm.fif
    ton_oracle_runvm_lib.fif
  smoke/                  -- tracked reference snapshots (moved from _runs/_smoke_*)
  runs/                   -- gitignored, runtime output from oracle runs
```

### What gets deleted

- `oracle/_runs/` directory structure (contents moved to `oracle/smoke/` if tracked,
  otherwise deleted)

---

## 13. Reorganize Documentation

### What it is now

`docs/` contains `START_HERE.md`, `implementing-instructions.md`, `linear-backlog.md`,
`spec-and-ton-context.md`, `README.md`, and `progress/` subdirectory.
`diff-testing-plan.md` and `AGENTS.md` are at root.

### What replaces it

```
docs/
  README.md               -- doc index
  start-here.md           -- onboarding guide
  architecture/
    overview.md           -- Model / Semantics / Native / Validation layers explained
    host-interface.md     -- why Host exists, how proof users benefit
    dependency-graph.md   -- the strict import rules, with diagram
  development/
    implementing-instructions.md    -- updated for new structure
    writing-tests.md      -- how to write InstrSuite (unit, oracle, fuzz)
    running-tests.md      -- all test/validation commands
  validation/
    diff-testing.md       -- diff-test architecture, fixture management
    oracle.md             -- oracle validation pipeline
  progress/
    README.md
    tvm_spec_index.json
    tvm_spec_index.csv
    instructions_full.csv
```

### What gets deleted or moved

- `diff-testing-plan.md` at root → content absorbed into `docs/validation/diff-testing.md`
- `AGENTS.md` at root → delete (the new docs structure replaces it)
- `docs/linear-backlog.md` → keep if Linear integration is still active
- `docs/spec-and-ton-context.md` → absorb into `docs/architecture/overview.md`

---

## 14. Update `.github/workflows/`

### `ci.yml` changes

- Build targets: `lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests`
- Run tests: `lake exe tvm-lean-tests`
- Run curated diff tests: `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit`
- Generate coverage report: `lake exe tvm-lean-coverage -- --format json --out build/coverage.json`
- Upload coverage report as artifact
- Optionally: fail if coverage regresses (no instruction loses status)

### `nightly.yml` changes

- Full oracle parity suite
- Fuzz suites with larger counts
- Mainnet diff-test sweep
- Extended coverage report

---

## 15. Update Root Files

### `README.md`

Rewrite to reflect the new structure. Should cover:

- What the project is (one paragraph)
- The four-layer architecture (one paragraph each)
- Quick start: build, run tests, run diff tests
- Links to detailed docs
- License

### `CONTRIBUTING.md`

New file. Should cover:

- How to add a new instruction (implement handler, add test suite, run oracle)
- How to write tests (link to `docs/development/writing-tests.md`)
- Code style and conventions
- PR process

### `lakefile.lean`

Complete rewrite with the new library and executable targets as described in
sections 9 and 10.

### `.gitignore`

Update to reflect new directory structure:

- `diff-test/work/` → ignored
- `diff-test/reports/` → ignored
- `oracle/runs/` → ignored
- `.lake/` → already ignored
- Remove entries for old directories that no longer exist

---

## 16. Update `tools/`

### `gen_spec_index.py`

Extend to also generate `TvmLean/Spec/Index.lean` (section 5).

### `gen_test_scaffold.py`

Rewrite to target the new `Tests/Instr/<Family>/<INSTR>.lean` structure:

- Read from generated spec index
- Create skeleton files for missing instructions
- Generate `Tests/All.lean`

### `gen_instruction_progress.py`

Update to read from the new coverage report format instead of the old test structure.

### Other tools

- `run_diff_tests.sh` → update paths if fixture directories changed
- `run_oracle_validate*.sh` → update executable names/paths if needed
- `linear_sync.py`, `linear_subissues.py` → update if instruction ID format changed
- `codex_autopr.py`, `github_automerge.py`, `github_linear_backflow.py` → probably
  unchanged, verify

### `promote_fixture.py`

New script (section 11).

---

## 17. Files That Don't Change

For completeness — these survive the refactor untouched or with minimal changes:

- `c/*` — all native C/C++ source files stay as-is. The only change is that they
  are now linked only by `TvmLeanNative` instead of the monolithic `TvmLean`.
- `fixtures/*.boc.hex` — small standalone fixtures, unchanged.
- `third_party/tvm-specification/*` — vendored spec, unchanged.
- `lean-toolchain` — unchanged.
- `LICENSE` — unchanged.
- `.env.example` — unchanged.

---

## 18. Development Workflow And What Gets Run When

This section describes the day-to-day development workflow after the refactor is
complete. It covers what to run locally during development, what to run before
committing, and what CI and nightly automation handle.

### Every edit cycle (after any code change)

```
lake build
```

This is the first gate. If it fails, nothing else matters. With `defaultTargets`
set to Model + Semantics, a bare `lake build` only builds the proof-grade core.
During active development in this repo, run the full build explicitly:

```
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
```

Or just build the specific library being worked on plus its dependents.

### After implementing or modifying any instruction handler

1. **Build:**
   ```
   lake build TvmLeanSemantics
   ```

2. **Run the per-instruction test suite** (once cases exist for that instruction):
   ```
   lake exe tvm-lean-tests -- --filter <InstrId>
   ```
   This runs unit, oracle, and fuzz cases for that specific instruction.

3. **Run the curated diff-test set** to check for regressions:
   ```
   lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
   ```

4. **Run the coverage probe** for the touched instruction to verify it reports
   as `ok` (not `stub` or `missing`):
   ```
   lake exe tvm-lean-progress -- --filter <InstrId>
   ```

### Before committing / opening a PR

Run the full local validation sweep. This is what CI will run, so catching failures
here avoids round-trips:

```
lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests
lake exe tvm-lean-tests
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-coverage -- --format json --out build/coverage.json
```

Check the coverage report for regressions — no instruction should lose status
(go from `ok` to `stub` or `missing`) compared to the previous commit.

### Periodically during development (not every commit)

**Full oracle parity run** — runs all hand-crafted oracle cases against `fift runvmx`
for every instruction that has cases. This is slower because it invokes `fift` per case:

```
lake exe tvm-lean-tests -- --oracle-only
```

Or via the oracle-specific executable with full matrix options:

```
tools/run_oracle_validate.sh
```

**Full fuzz run** — runs all fuzz specs with their configured counts and seeds:

```
lake exe tvm-lean-tests -- --fuzz-only
```

This is the slowest local run. Run it after significant changes to instruction
semantics, after implementing new instructions, or before releases.

**Extended diff-test runs** — run against the full curated fixture set, not just
the CI subset:

```
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/curated --strict-exit
```

**Coverage report review** — generate and inspect the full coverage table:

```
lake exe tvm-lean-coverage -- --format md --out build/coverage.md
```

Review this regularly to identify gaps and prioritize next instructions to cover.

### Fixture collection and promotion (as needed)

When collecting new mainnet transaction fixtures:

```
cd diff-test/collector && npm run collect -- <args>
```

New fixtures land in `diff-test/work/` (gitignored). Test them:

```
lake exe tvm-lean-diff-test -- --dir diff-test/work --strict-exit
```

Promote good fixtures to the tracked curated set:

```
python tools/promote_fixture.py diff-test/work/<fixture>.json
```

### Spec index regeneration (rare, only when vendored spec updates)

When `third_party/tvm-specification/` is updated to a new upstream commit:

```
python tools/gen_spec_index.py
```

This regenerates `TvmLean/Spec/Index.lean`, `docs/progress/tvm_spec_index.json`,
and related index files. Then regenerate test skeletons for any new instructions:

```
python tools/gen_test_scaffold.py
```

### What CI runs on every PR

- Full build of all Lake targets
- `lake exe tvm-lean-tests` (all registered unit, oracle, and fuzz cases)
- `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit`
- Coverage report generation and upload as artifact
- Coverage regression check (no instruction loses status)

CI must stay fast. The oracle and fuzz test suites run in CI only use the cases
registered in the committed test files — this is intentionally a smaller set than
a full oracle or fuzz sweep. If oracle or fuzz runs become too slow for CI, the
registered case counts can be reduced while nightly picks up the full load.

### What nightly automation runs

- Full oracle parity suite for all instructions with cases
- Fuzz suites with larger iteration counts
- Mainnet diff-test sweep (collector fetches recent transactions, runs them)
- Extended coverage report
- Results uploaded as artifacts, failures create alerts

### What tooling scripts do and when to run them

| Script | Purpose | When to run |
|---|---|---|
| `tools/gen_spec_index.py` | Regenerate spec index from vendored spec | After updating `third_party/tvm-specification/` |
| `tools/gen_test_scaffold.py` | Generate/update test skeletons and `All.lean` | After spec index changes, or after adding new instruction files manually |
| `tools/gen_instruction_progress.py` | Generate full progress table | When reviewing overall status |
| `tools/promote_fixture.py` | Move fixture from work to curated | After verifying a new fixture is valuable |
| `tools/run_diff_tests.sh` | Run diff tests (convenience wrapper) | During development, equivalent to `lake exe tvm-lean-diff-test` |
| `tools/run_oracle_validate.sh` | Run oracle validation | Periodically, before releases |
| `tools/run_oracle_validate_matrix.sh` | Full matrix oracle run | Before releases, or nightly |
| `tools/run_oracle_validate_extensive.sh` | Extensive oracle sweep | Rare, deep validation |
| `tools/linear_sync.py` | Sync instruction backlog with Linear | When updating project tracking |
| `tools/linear_subissues.py` | Create Linear sub-issues | When breaking down work |
| `tools/codex_autopr.py` | Auto-create PRs for completed tasks | Runs as daemon |
| `tools/github_automerge.py` | Auto-merge approved PRs | Runs as daemon |
| `tools/github_linear_backflow.py` | Sync PR closures back to Linear | Runs as daemon |

---

## Verification Checklist

After the refactor is complete, verify each of these properties. Every single one
must be true.

### Structural integrity

- [ ] `TvmLean/Core/` does not exist.
- [ ] `TvmLean/Core/Prelude.lean` does not exist.
- [ ] No file named `*Main.lean` exists at repository root.
- [ ] `Tests.lean` does not exist at repository root.
- [ ] No `TvmLean/DiffTest.lean`, `TvmLean/OracleValidate.lean`, or
      `TvmLean/CellDiff.lean` exists.
- [ ] No directory matching `diff-test/fixtures_fift_tmp*` exists.
- [ ] No directory matching `diff-test/fixtures_fift_focus` exists.
- [ ] `diff-test/focus_report.json` does not exist.
- [ ] `oracle/_runs/` does not exist (replaced by `oracle/runs/` and `oracle/smoke/`).

### Dependency rules

- [ ] No file under `TvmLean/Model/` imports anything from `TvmLean/Semantics/`,
      `TvmLean/Native/`, or `TvmLean/Validation/`.
- [ ] No file under `TvmLean/Semantics/` imports anything from `TvmLean/Native/`
      or `TvmLean/Validation/`.
- [ ] No file under `TvmLean/Model/` or `TvmLean/Semantics/` contains `@[extern]`.
- [ ] All `@[extern]` declarations live exclusively in `TvmLean/Native/Extern/`.
- [ ] `execInstr`, `step`, and `run` all take `Host` as a parameter.
- [ ] No crypto handler calls an extern function directly — all go through `Host`.

### Build and test

- [ ] `lake build TvmLeanModel` succeeds without any C compiler.
- [ ] `lake build TvmLeanSemantics` succeeds without any C compiler.
- [ ] `lake build TvmLeanNative` succeeds and links C objects.
- [ ] `lake build TvmLeanValidation` succeeds.
- [ ] `lake build TvmLeanTests` succeeds.
- [ ] All executables build: `lake build tvm-lean tvm-lean-tests tvm-lean-diff-test`
      (and others).
- [ ] `lake exe tvm-lean-tests` runs (suites are empty but harness works).
- [ ] `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit` passes.
- [ ] `lake exe tvm-lean-coverage` produces a report showing all instructions with
      their implementation status.

### Stub visibility

- [ ] `VmError.unimplemented` variant exists.
- [ ] Every known stub instruction throws `unimplemented` instead of silently no-oping.
- [ ] Coverage report distinguishes `ok`, `stub`, and `missing` for each instruction.

### Test infrastructure

- [ ] `Tests/Harness/Registry.lean` defines `InstrSuite`, `UnitCase`, `OracleCase`,
      `FuzzSpec`.
- [ ] `Tests/Harness/OracleHarness.lean` can run a case on Lean and invoke fift.
- [ ] `Tests/Harness/Coverage.lean` reads the registry and spec index to produce
      coverage reports.
- [ ] A skeleton file exists under `Tests/Instr/` for every instruction in the spec
      index.
- [ ] `Tests/All.lean` exists and imports all instruction skeleton files.

### Documentation

- [ ] `docs/architecture/overview.md` explains the four-layer architecture.
- [ ] `docs/development/writing-tests.md` explains how to write an `InstrSuite`.
- [ ] `docs/development/implementing-instructions.md` is updated for the new paths.
- [ ] `README.md` reflects the new project structure.
- [ ] `CONTRIBUTING.md` exists.

### Cleanliness

- [ ] `diff-test/work/` is in `.gitignore`.
- [ ] `oracle/runs/` is in `.gitignore`.
- [ ] No orphaned imports (nothing imports a deleted module).
- [ ] `lake build` from a fresh clone with `defaultTargets` builds only Model
      and Semantics.

---

## What Comes After (Out Of Scope For This Refactor)

Once the structure is in place:

1. **Fill in per-instruction oracle test cases.** Go instruction by instruction,
   write hand-crafted `OracleCase`s that cover edge cases, boundary conditions,
   type variations, and error paths. This is the bulk of the work going forward.

2. **Fill in per-instruction fuzz specs.** Write generators for each instruction
   family. Start with arithmetic (easiest to generate valid inputs), expand.

3. **Kill stubs.** The coverage report now shows every stub. Implement them one
   by one, adding test suites along the way.

4. **Begin proof work.** With Model and Semantics clean and Host-parameterized,
   start writing Lean proofs about specific instructions or VM properties.

5. **Publish as a Lean package.** Once the API is stable, publish so external
   projects can `require TvmLean` and use Model + Semantics for their proofs.
