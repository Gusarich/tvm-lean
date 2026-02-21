# Running Tests

Use this page as the test command matrix for local development and pre-PR validation.

## Build/test matrix

| Category | Command | Signal | Typical cadence |
|---|---|---|---|
| Build sanity | `lake build` | whole workspace compiles | every local session |
| Core libs gate | `lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests` | model/semantics/native/validation/tests build | pre-push |
| Contracts gate | `lake build TvmLeanContracts` | contract modules and proofs compile | when touching `Contracts/` or proof APIs |
| Standalone contract proof | `lake env lean Contracts/<Name>/Proof.lean` | one contract example proof (and its `Program`/`Spec` imports) compiles | fast local edit loop |
| Harness full sweep | `lake exe tvm-lean-tests` | unit + oracle + fuzz suites | pre-PR |
| Diff-test CI fixtures | `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit` | deterministic parity set | pre-push / pre-PR |
| Coverage report | `lake exe tvm-lean-coverage -- --format json --out build/coverage.json` | instruction coverage snapshot | pre-PR |

## Runtime budget lanes (explicit)

Use these budget classes to keep local/CI feedback predictable:

| Budget class | Target wall-clock | Command set | When to run |
|---|---|---|---|
| Fast loop | ≤ 2–5 min | `lake build TvmLeanSemantics` + `lake exe tvm-lean-tests -- --filter <InstrId>` + `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/smoke --strict-exit` | during active implementation |
| Per-PR gate | ≤ 10–20 min | `lake build TvmLeanModel TvmLeanSemantics TvmLeanNative TvmLeanValidation TvmLeanTests` + `lake exe tvm-lean-tests` + `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit` + `lake exe tvm-lean-coverage -- --format json --out build/coverage.json` | before opening/updating a PR |
| Nightly / scheduled | 20+ min (can be much longer) | `lake exe tvm-lean-tests -- --oracle-only` + `lake exe tvm-lean-tests -- --fuzz-only` + curated/sharded diff runs + `tools/run_oracle_validate.sh` | nightly CI, release hardening, large refactors |

Per-PR keeps deterministic gates tight; nightly carries expensive randomized/parity sweeps.
If nightly runtime grows, shard diff runs (`tools/run_diff_tests.sh --shards <N>`) and raise oracle parallelism (`tools/run_oracle_validate.sh --jobs <N>`).

## Harness mode matrix

`tvm-lean-tests` supports these focused modes:

| Mode | Command | Best for |
|---|---|---|
| All modes (default) | `lake exe tvm-lean-tests` | final local confidence sweep |
| Single instruction | `lake exe tvm-lean-tests -- --filter <InstrId>` | tight implementation loop |
| Unit-only | `lake exe tvm-lean-tests -- --unit-only` | fast deterministic assertions |
| Oracle-only | `lake exe tvm-lean-tests -- --oracle-only` | Lean vs reference parity checks |
| Fuzz-only | `lake exe tvm-lean-tests -- --fuzz-only` | randomized stress coverage |

`--filter` is exact (`suite.id.name = <InstrId>`), so use the precise instruction id.

## Diff fixture matrix

| Fixture set | Command | Purpose | Cost |
|---|---|---|---|
| Smoke | `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/smoke --strict-exit` | fastest fixture sanity check | very low |
| CI | `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit` | tracked deterministic gate | low |
| Curated (if present) | `lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/curated --strict-exit` | broader promoted fixture set | medium/high |
| Work scratch | `lake exe tvm-lean-diff-test -- --dir diff-test/work --strict-exit` | local fixture development | variable |

For sharded large runs: `tools/run_diff_tests.sh --dir diff-test/fixtures/ci --shards 12 --strict-exit`.

## Fast local gates

```sh
lake build TvmLeanSemantics
lake exe tvm-lean-tests -- --filter <InstrId>
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
lake exe tvm-lean-progress -- --summary
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

Coverage review:

```sh
lake exe tvm-lean-coverage -- --format md --out build/coverage.md
lake exe tvm-lean-coverage -- --format tsv --out build/coverage.tsv
```

Standalone contract example checks:

```sh
lake env lean Contracts/ToyCounter/Proof.lean
lake env lean Contracts/DictCounter/Proof.lean
lake env lean Contracts/FlowGate/Proof.lean
lake env lean Contracts/MsgParser/Proof.lean
lake env lean Contracts/NonceGuard/Proof.lean
lake env lean Contracts/LoopCounter/Proof.lean
```

## Anti-patterns to avoid

- Running full `tvm-lean-tests` on every small edit instead of narrowing with `--filter`.
- Treating `--oracle-only` or `--fuzz-only` as complete coverage by itself.
- Running diff tests without `--strict-exit` for gate checks.
- Forgetting the `--` separator before runner flags.

## Troubleshooting quick map

| Symptom | Usually means | Fix |
|---|---|---|
| `unknown argument: --filter` (or other flag) | flag parsed by `lake`, not app | add `--`: `lake exe tvm-lean-tests -- --filter ADD` |
| `missing required argument: --case <file.json> or --dir <dir>` | diff-test input not specified | pass `--dir ...` (or `--case ...`) |
| `suites=0` in test summary | filter id does not match any suite | use exact suite id spelling/casing |
| diff-test exits nonzero with skips/errors | strict gate caught non-pass outcomes | inspect failing fixture, rerun with trace flags if needed |
