# Progress Tracking

This directory contains generated progress/index files derived from the vendored TVM instruction specification.

The **authoritative backlog** is tracked in Linear (one issue per instruction/alias). These files are snapshots/views
generated from the pinned spec + Linear (and may include legacy fallback markers).

## Files

- `tvm_spec_index.json` / `tvm_spec_index.csv`: compact index of all TVM instructions + Fift aliases.
- `instructions_full.csv`: progress table for **every** TVM instruction (919) and every Fift alias (116).
  - If `LINEAR_API_KEY` is available (env or `.env`), `implemented/tested` are derived from Linear `ws/impl` and
    `ws/tests` subissues.
  - Otherwise it falls back to the legacy seed `instructions.csv`.
- `instructions.csv`: legacy/manual seed list (only used as a fallback).

## Editing

Do **not** edit `tvm_spec_index.*` or `instructions_full.csv` manually — they are generated.

If you want a completely offline workflow (no Linear API), update the legacy seed `instructions.csv` and regenerate
with `--source legacy`.

## Regenerate

```sh
python3 tools/gen_spec_index.py
python3 tools/gen_instruction_progress.py
```
