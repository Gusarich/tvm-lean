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

Required for expected-state generation:

- TON `fift` binary with `runvmx`
- `Fift.fif` library path

Set:

```sh
export TON_FIFT_BIN=/path/to/ton/build/crypto/fift
export TON_FIFT_LIB=/path/to/ton/crypto/fift/lib
```

## Collect fixtures

```sh
npm run collect -- --tx <TX_HASH> --out-dir ../fixtures
```

The collector also embeds the relevant global-config parameters needed for fee opcodes:
- `stack_init.config_mc_fwd_prices_boc` (ConfigParam 24, `MsgForwardPrices` for masterchain)
- `stack_init.config_fwd_prices_boc` (ConfigParam 25, `MsgForwardPrices` for basechain)

Expected state is always computed by executing TVM in TON C++ (`fift` + `runvmx`) and storing:

- `expected.exit_code`
- `expected.gas_used`
- `expected.c4_boc`
- `expected.c5_boc`

Precompiled contracts (ConfigParam 45 hits for `mycode`) are not supported by the `runvmx` oracle path and are skipped by `sweep`.

Or from a file with one tx hash per line:

```sh
npm run collect -- --tx-file tx_hashes.txt --out-dir ../fixtures
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

Run Lean on the fly in batches:

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
- In `--run-lean` mode, fixtures are written to `out-dir/batch/` and deleted between batches to save disk; use `--keep-fixtures` to also keep a copy in `out-dir/`.
- Add `--skip-unsupported` to classify `invOpcode` / unsupported BOC parse errors as `SKIP` (otherwise they are reported as `FAIL`/`ERROR`).
- Add `--trace-failures --trace-max <N>` to include Lean VM step traces in results for non-PASS cases (useful for debugging).
- Add `--trace-all --trace-max <N>` to include Lean VM step traces for **every** case (including PASS).
- By default, `sweep` (like `collect`) only includes the **first transaction per account per masterchain block**. Use `--allow-nonfirst` to include all, but results may be unreliable until we implement in-block state replay.
- For huge ranges, expect rate limits; use your own `TONCENTER_API_KEY` / `DTON_API_KEY` if needed.
- `diff-test/fixtures/*.json` and `diff-test/*.jsonl` are intended to be local outputs and are gitignored (only `smoke_*.json` is checked in).

## Run in Lean

```sh
lake exe tvm-lean-diff-test -- --case diff-test/fixtures/<TX_HASH>.json
```
