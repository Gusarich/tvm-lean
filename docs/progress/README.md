# Progress Tracking

This directory contains generated progress/index files derived from the vendored TVM instruction specification.

The **authoritative backlog** is tracked in Linear (one issue per instruction/alias). These files are snapshots/views
generated from the pinned spec (and may include legacy “implemented/tested” markers).

## Files

- `tvm_spec_index.json` / `tvm_spec_index.csv`: compact index of all TVM instructions + Fift aliases.
- `instructions_full.csv`: progress table for **every** TVM instruction (919) and every Fift alias (116).
- `instructions.csv`: legacy/manual list used early on (kept for now).

## Editing

Do **not** edit `tvm_spec_index.*` or `instructions_full.csv` manually — they are generated.

If you want to keep lightweight “implemented/tested” markers in-repo for now, update the legacy seed
`instructions.csv` and regenerate `instructions_full.csv`.

## Regenerate

```sh
python3 tools/gen_spec_index.py
python3 tools/gen_instruction_progress.py
```
