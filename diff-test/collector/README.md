# Diff-test fixture collector (txtracer-core)

Collects per-transaction JSON fixtures for `tvm-lean` diff testing, using `txtracer-core`.

## Setup

From `diff-test/collector`:

```sh
npm install
npm run build
```

Optional (recommended): set your own API keys to avoid rate limits:

- `TONCENTER_API_KEY`
- `DTON_API_KEY`

## Collect fixtures

```sh
npm run collect -- --tx <TX_HASH> --out-dir ../fixtures
```

Or from a file with one tx hash per line:

```sh
npm run collect -- --tx-file tx_hashes.txt --out-dir ../fixtures
```

To include strict end-state expectations (`expected.c4_boc` / `expected.c5_boc` / `expected.c7`) via TON Sandbox emulation:

```sh
npm run collect -- --tx <TX_HASH> --expected-state --out-dir ../fixtures
```

By default, the collector skips transactions that are *not the first one for that account inside the masterchain block*
(because `tvm-lean` would need the pre-transaction state rolled forward within the block). To disable that filter:

```sh
npm run collect -- --tx <TX_HASH> --allow-nonfirst
```

## Sweep a time range

Enumerate transactions from **workchain 0 and -1** by masterchain blocks in a time range and (optionally) run the Lean diff runner.

Collect fixtures only:

```sh
npm run sweep -- --since 2026-01-27 --max-blocks 10 --out-dir ../fixtures
```

Run Lean on the fly in batches (skipping invOpcode / unsupported-opcode failures):

```sh
# from repo root, build the diff runner once
(cd ../.. && lake build tvm-lean-diff-test)

# then sweep + run
npm run sweep -- \
  --since 2026-01-27 \
  --run-lean \
  --batch-size 200 \
  --results ../results.jsonl
```

Notes:
- `--max-txs` limits **transactions scanned**, not fixtures produced. Use `--max-fixtures <N>` if you want to run exactly N diff tests.
- In `--run-lean` mode, fixtures are written to `out-dir/_batch/` and deleted between batches to save disk; use `--keep-fixtures` to also keep a copy in `out-dir/`.
- Add `--trace-failures --trace-max <N>` to include Lean VM step traces in results for non-PASS cases (useful for debugging).
- Add `--trace-all --trace-max <N>` to include Lean VM step traces for **every** case (including PASS).
- Add `--expected-state` to populate `expected.c4_boc` / `expected.c5_boc` / `expected.c7` using TON Sandbox emulation (slower, but enables strict end-state comparisons).
- By default, `sweep` (like `collect`) only includes the **first transaction per account per masterchain block**. Use `--allow-nonfirst` to include all, but results may be unreliable until we implement in-block state replay.
- For huge ranges, expect rate limits; use your own `TONCENTER_API_KEY` / `DTON_API_KEY` if needed.
- `diff-test/fixtures/*.json` and `diff-test/*.jsonl` are intended to be local outputs and are gitignored (only `smoke_*.json` is checked in).

## Run in Lean

```sh
lake exe tvm-lean-diff-test -- --case diff-test/fixtures/<TX_HASH>.json
```
