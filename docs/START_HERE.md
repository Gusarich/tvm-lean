# tvm-lean — Start Here

`tvm-lean` is an executable Lean model of a subset of the TON Virtual Machine (TVM), structured so we can incrementally:

- implement more opcodes (toward full coverage)
- add regression tests (unit + mainnet diff tests)
- later add proofs/invariants without rewriting the core

The **instruction backlog** comes from a vendored/pinned TVM JSON specification and is tracked in **Linear** (one issue per instruction + one per Fift alias).

## Quickstart

Build:

```sh
lake build
```

Run the built-in “counter” demo (assembles cp0 in Lean):

```sh
lake exe tvm-lean
```

Run from a BOC containing a *code* cell:

```sh
lake exe tvm-lean -- --boc /path/to/code.boc --c4 41 --fuel 200
```

Run unit tests:

```sh
lake exe tvm-lean-tests
```

Run offline diff regression tests (curated mainnet fixtures):

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

## C++ oracle instruction validation (per-opcode)

For instruction-level correctness, there is an oracle-based validator that runs each TVM opcode:

- once in the **TON C++ reference TVM** (via `fift` + `runvmx`)
- once in **Lean**
- then compares exit code, gas used, `c4`/`c5` hashes, and canonicalized stack

This is deterministic (no fuzz/random) and is meant for generating 10–20 meaningful cases per opcode.

Prereqs:

- local TON repo built with `fift` available at `/Users/daniil/Coding/ton/build/crypto/fift`
  - or set `TON_FIFT_BIN` / `TON_FIFT_LIB`

Build the oracle validator:

```sh
lake build tvm-lean-oracle-validate
```

Run a single opcode:

```sh
./.lake/build/bin/tvm-lean-oracle-validate --only ADDINT --variants 20 --code-variants 8 --cases 20 --verbose
```

Run a sweep in parallel and store logs:

```sh
tools/run_oracle_validate.sh --jobs 12 --variants 20 --code-variants 8 --cases 20 --out oracle/_runs/latest
```

Optional env overrides:

```sh
TON_FIFT_BIN=/Users/daniil/Coding/ton/build/crypto/fift
TON_FIFT_LIB=/Users/daniil/Coding/ton/crypto/fift/lib
TVMLEANTON_ORACLE_LIB_FIF=tools/ton_oracle_runvm_lib.fif
```

## Mainnet diff tests (collecting fixtures)

You can diff-test against real mainnet transactions by collecting JSON fixtures from Toncenter, then running
the Lean diff-test runner on them.

Prereqs:

- Node.js + `npm`
- Optional: set `TONCENTER_API_KEY` to avoid rate limits (Toncenter)

Build the Lean diff-test runner:

```sh
lake build tvm-lean-diff-test
```

Install + build the fixture collector:

```sh
cd diff-test/collector
npm install
npm run build
```

Collect a single transaction fixture:

```sh
npm run collect -- --tx <TX_HASH> --out-dir ../fixtures/manual
```

Sweep and *run* (batch) diff-tests over ~5000 fixtures, streaming results to `diff-test/results.jsonl`:

```sh
TONCENTER_API_KEY=... npm run sweep -- --since 2026-02-01 --max-fixtures 5000 --run-lean --batch-size 200 --skip-unsupported --results ../results.jsonl --keep-fixtures
```

Run the diff-test runner directly over a fixtures directory:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/manual --max-cases 5000 --skip-unsupported --out diff-test/report.json --strict-exit
```

## Repo map

- `TvmLean/Core.lean`: thin re-export of the core VM model (see `TvmLean/Core/Prelude.lean`, `TvmLean/Core/Exec.lean`, `TvmLean/Core/Step.lean`)
- `TvmLean/Boc.lean`: BOC parsing/serialization (“untrusted input layer”)
- `Tests.lean`: small unit tests + encode/decode roundtrip checks
- `TvmLean/DiffTest.lean`, `DiffTestMain.lean`: mainnet diff-test runner for JSON fixtures
- `diff-test/collector/`: TypeScript fixture collector (optional; used to generate new fixtures)
- `third_party/tvm-specification/`: vendored TVM spec (pinned) used to generate instruction indexes
- `docs/progress/`: generated instruction indexes/tables

## Where the instruction backlog lives

- Linear backlog conventions: `docs/linear-backlog.md`
- Spec pin + mapping to TON C++: `docs/spec-and-ton-context.md`

To start implementing opcodes, use: `docs/implementing-instructions.md`
