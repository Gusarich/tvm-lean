# Diff Testing

Diff testing compares Lean execution against expected fixture outputs derived from
TON mainnet data.

## Directory layout

- `diff-test/fixtures/ci/`: tracked deterministic CI subset
- `diff-test/fixtures/smoke/`: tiny tracked smoke set
- `diff-test/fixtures/curated/`: tracked promoted fixtures
- `diff-test/work/`: gitignored scratch fixtures
- `diff-test/reports/`: gitignored run outputs
- `diff-test/scripts/pretty_trace.py`: trace inspection helper
- `diff-test/collector/`: fixture collection/generation toolchain

## Run diff tests

CI subset:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

Curated full set:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/curated --strict-exit
```

Scratch work directory:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/work --strict-exit
```

## Collect and promote fixtures

Collect with TypeScript collector (example):

```sh
cd diff-test/collector
npm run sweep -- --since 2026-02-01 --until 2026-02-02 --max-fixtures 200 --keep-fixtures
```

Promote validated fixtures from `work` to tracked curated set:

```sh
python3 tools/promote_fixture.py diff-test/work/<fixture>.json
```

## Sharded runs

For large local sweeps:

```sh
tools/run_diff_tests.sh --dir diff-test/fixtures/curated --shards 12 --strict-exit
```

Results are written under `diff-test/reports/`.
