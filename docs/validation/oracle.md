# Oracle Validation

Oracle validation runs Lean and TON Fift `runvmx` on the same instruction cases and
compares key outputs.

## What is compared

- exit code
- gas used
- stack canonicalization
- relevant register outputs (for supported case forms)

## Layout

- `oracle/fif/`: Fift runner scripts used by the oracle bridge
- `oracle/smoke/`: tracked smoke snapshots
- `oracle/runs/`: gitignored run outputs

## Prerequisites

- built `fift` from TON monorepo
- `TON_FIFT_BIN` and `TON_FIFT_LIB` environment variables (if non-default)

## Common commands

Single instruction via Lean executable:

```sh
lake exe tvm-lean-oracle -- --only ADDINT --variants 20 --code-variants 8 --cases 20
```

Parallel instruction sweep:

```sh
tools/run_oracle_validate.sh --jobs 12 --variants 20 --code-variants 8 --cases 20
```

Multi-seed matrix:

```sh
tools/run_oracle_validate_matrix.sh --seeds 1,7,42 --variants 64 --code-variants 64 --cases auto
```

Extensive stress sweep:

```sh
tools/run_oracle_validate_extensive.sh
```
