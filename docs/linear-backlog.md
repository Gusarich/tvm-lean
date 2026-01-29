# Linear Backlog Conventions

This repo uses Linear to track the full TVM instruction backlog from the vendored spec.

## Projects

- `Instruction Coverage (TVM Spec)`: one issue per instruction / alias.
- `Infra & Automation`: tooling + maintenance work.
- `Diff Testing & Mainnet Sweep`: fixture collection + regression work.
- `Proof Roadmap`: invariants + proof milestones.

## Labels

- `kind/tvm`: TVM instruction issues.
- `kind/fift-alias`: Fift-only alias issues.
- `cat/*`: spec categories (e.g. `cat/arithmetic`, `cat/cell`, …).
- `ws/*`: workstream markers used when splitting work (e.g. `ws/impl`, `ws/tests`, `ws/spec-audit`, `ws/proof`).

## Unique keys

Every instruction/alias issue starts with a unique key in its description so it can be found and synced:

- TVM instruction: `SpecKey: tvm::<INSTRUCTION_NAME>`
- Fift alias: `SpecKey: fift::<ALIAS_NAME>`

## Backlog hierarchy

- Epic: `TVM-7` (“TVM Spec Backlog (919 TVM + 116 Fift aliases)”)
- Under the epic: one issue per category (e.g. `Category: arithmetic (246)`).
- Under each category: one issue per instruction/alias.

## Syncing

The source of truth for the instruction/alias list is `docs/progress/tvm_spec_index.json`.

To bulk create/update Linear issues from that file, use `tools/linear_sync.py` (dry-run by default):

```sh
python3 tools/linear_sync.py
LINEAR_API_KEY="lin_api_..." python3 tools/linear_sync.py --apply
```

Tip: put `LINEAR_API_KEY="lin_api_..."` in a local `.env` at the repo root and the sync script will pick it up.

To normalize older issue descriptions to the canonical template (adds encoding/TON refs/checklists where missing):

```sh
python3 tools/linear_sync.py --apply --sync-descriptions
```

Verify that Linear contains **every** spec entry:

```sh
python3 tools/linear_sync.py --verify
```
