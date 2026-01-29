# TVM Spec + TON Monorepo Context

This repo uses the instruction catalog from `ton-blockchain/tvm-specification` as the **source of truth** for:

- the complete list of TVM instructions (currently 919)
- Fift-only alias mnemonics (currently 116)
- bytecode layout metadata (prefix/ranges, argument decoding, TLB)
- links to the reference C++ implementation in the TON monorepo (file/function/line + commit hash)

## Vendored spec (pinned)

The spec is vendored in:

- `third_party/tvm-specification/tvm-specification.json`
- `third_party/tvm-specification/schema.json`
- `third_party/tvm-specification/README.md`
- `third_party/tvm-specification/LICENSE`
- `third_party/tvm-specification/UPSTREAM.json` (upstream commit pin)

## Generated indexes

From the vendored JSON, we generate a compact index and a progress table:

- `docs/progress/tvm_spec_index.json` (machine-readable)
- `docs/progress/tvm_spec_index.csv` (spreadsheet-friendly)
- `docs/progress/instructions_full.csv` (progress tracking for **every** TVM + Fift alias instruction)

Regenerate:

```sh
python3 tools/gen_spec_index.py
python3 tools/gen_instruction_progress.py
```

## Mapping an instruction to TON C++

Each TVM instruction in the spec may include `implementation` info:

- `commit_hash` (TON monorepo commit)
- `file_path`
- `line_number`
- `function_name`

Workflow for developers:

1. Clone the TON monorepo locally.
2. `git checkout <commit_hash>` from the spec entry.
3. Open `<file_path>` and jump to `<line_number>` / `<function_name>`.

This keeps `tvm-lean` lightweight: we **link** to TON C++ rather than vendoring the full monorepo here.

## Fift instructions

Fift instructions in the spec are aliases:

- each entry is `{ name, actual_name }`

We track these separately (and in Linear) to ensure alias expansion stays consistent with the underlying TVM instruction.

