# Progress Tracking

This directory contains generated progress/index files derived from the vendored TVM instruction specification.

## Files

- `tvm_spec_index.json` / `tvm_spec_index.csv`: compact index of all TVM instructions + Fift aliases.
- `instructions_full.csv`: progress table for **every** TVM instruction (919) and every Fift alias (116).
- `instructions.csv`: legacy/manual list used early on (kept for now).

## Regenerate

```sh
python3 tools/gen_spec_index.py
python3 tools/gen_instruction_progress.py
```

