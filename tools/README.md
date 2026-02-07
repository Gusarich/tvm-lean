# Tools

Small helper scripts for spec indexing, test scaffolding, validation runs, and backlog sync.

## Generate spec index

```sh
python3 tools/gen_spec_index.py
```

Outputs:

- `docs/progress/tvm_spec_index.json`
- `docs/progress/tvm_spec_index.csv`
- `TvmLean/Spec/Index.lean`

## Generate test scaffold + import index

```sh
python3 tools/gen_test_scaffold.py
```

Outputs:

- `Tests/Instr/<Family>/*.lean` skeletons (for missing instructions)
- `Tests/All.lean`

## Generate progress table

```sh
python3 tools/gen_instruction_progress.py
```

Outputs:

- `docs/progress/instructions_full.csv`

## Oracle parity sweeps (Lean vs Fift runvmx)

Run per-instruction parity in parallel (all instructions by default):

```sh
tools/run_oracle_validate.sh --jobs 12 --variants 20 --code-variants 8 --cases 20
```

Notes:

- `--cases auto` resolves to `variants * code-variants` to saturate the generated code×stack matrix.
- Real-time per-instruction PASS/FAIL lines are printed to stdout.
- Progress is also appended to `oracle/runs/<ts>/progress.log`.

Run the extensive all-instruction multi-seed matrix:

```sh
tools/run_oracle_validate_extensive.sh
```

## Collect and promote diff fixtures

Build collector and sweep:

```sh
export TON_FIFT_BIN=/path/to/ton/build/crypto/fift
export TON_FIFT_LIB=/path/to/ton/crypto/fift/lib

cd diff-test/collector
npm ci
npm run build
npm run sweep -- --since 2026-02-06 --until 2026-02-07 --max-fixtures 500 --keep-fixtures --out-dir ../work
```

Test scratch fixtures:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/work --strict-exit
```

Promote one validated fixture:

```sh
python3 tools/promote_fixture.py diff-test/work/<fixture>.json
```

## Sync Linear backlog (bulk)

This repo tracks the full TVM instruction backlog in Linear (one issue per instruction + one issue per Fift alias).

The `tools/linear_sync.py` script syncs Linear against `docs/progress/tvm_spec_index.json` using the Linear GraphQL API.

Dry-run:

```sh
python3 tools/linear_sync.py
```

Apply (creates/updates issues):

```sh
cp .env.example .env  # then set LINEAR_API_KEY=... (or export LINEAR_API_KEY in your shell)
LINEAR_API_KEY="lin_api_..." python3 tools/linear_sync.py --apply
```

The sync script also reads `LINEAR_API_KEY` from `.env` at the repo root (if present).

Normalize/upgrade older issue descriptions to the canonical template:

```sh
python3 tools/linear_sync.py --apply --sync-descriptions
```

Verify completeness (expects 919 TVM + 116 Fift):

```sh
python3 tools/linear_sync.py --verify
```

## Create standard subissues (ws/*)

To keep “one PR per issue”, we work in subissues labeled `ws/*` (impl/tests/diff/spec-audit/proof) under each
instruction issue.

Dry-run:

```sh
python3 tools/linear_subissues.py
```

Apply (bulk create missing subissues):

```sh
python3 tools/linear_subissues.py --apply
```

## Auto-create PRs for completed Codex tasks

When issues are delegated to Codex via Linear, Codex will usually post a comment and create a cloud task, but **PR
creation still requires a `/pr` call**. This helper automates that step.

Setup:

```sh
cp .env.example .env
# set CODEX_TOKEN=... in .env (kept local; gitignored)
```

One-shot run (recommended for cron):

```sh
python3 tools/codex_autopr.py --once
```

Daemon mode:

```sh
python3 tools/codex_autopr.py --watch --interval-seconds 60
```

Notes:

- The script only targets tasks whose Codex `environment_label` contains `tvm-lean` (configurable via `--env-label-substr`).
- Local state is stored in `.autopr/state.sqlite3` to avoid duplicate PR creation attempts.

## Auto-merge PRs (local daemon)

GitHub Actions scheduling is too coarse for “merge within ~1 minute”, and Codex approvals are currently signaled via
GitHub reactions. This daemon enforces the rules locally and merges PRs automatically.

Setup:

```sh
cp .env.example .env
# GitHub auth: set GITHUB_TOKEN=... in .env, or rely on an existing GitHub CLI login (`gh auth login`).
```

One-shot run:

```sh
python3 tools/github_automerge.py --once --verbose
```

Daemon mode (recommended):

```sh
python3 tools/github_automerge.py --watch --interval-seconds 60 --verbose
```

Defaults (configurable via flags):

- Only considers PRs whose head branch starts with `codex/` (set `--head-branch-prefix ''` to disable).
- Requires `Lean` + `Collector (TypeScript)` checks to pass.
- Requires a `+1` reaction from `chatgpt-codex-connector[bot]`.
- If a PR is behind `main`, it triggers “Update branch” and re-checks on the next cycle.

## GitHub → Linear backflow (close PR as “not planned”)

If you close a PR as “not planned”, it usually means the corresponding Linear issue should go back to `Todo` and be
unassigned from Codex.

Setup:

```sh
cp .env.example .env
# set LINEAR_API_KEY=... in .env (kept local; gitignored)
# GitHub auth: set GITHUB_TOKEN=... in .env, or rely on an existing GitHub CLI login (`gh auth login`).
```

One-shot run:

```sh
python3 tools/github_linear_backflow.py --once --verbose
```

Daemon mode:

```sh
python3 tools/github_linear_backflow.py --watch --interval-seconds 60 --verbose
```

Notes:

- Only scans PRs whose head branch starts with `codex/` by default (set `--head-branch-prefix ''` to disable).
- Detects the Linear issue id from the PR title / branch (e.g. `TVM-5997`).
- Resets the Linear issue state to `Todo` and clears assignee/delegate if it looks like Codex.
