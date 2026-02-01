# Implementing TVM Instructions

This repo tracks **one Linear issue per TVM instruction** (and one per Fift alias) based on the vendored spec.
Each issue description is intentionally a “mini-brief”: it points you to the spec entry and the reference TON C++ implementation.

## 1) Pick work (Linear)

This repo uses a **parent + subissue** model:

- Parent issue: `Instr: <NAME>` / `Fift: <ALIAS> -> <ACTUAL>` (spec context + TON refs)
- Work issues: child subissues labeled `ws/*` (each should be closed by a single PR)

Pick a work subissue under an instruction with:

- `kind/tvm` (or `kind/fift-alias` for aliases)
- a `cat/*` label matching the spec category
- one `ws/*` label (e.g. `ws/impl`, `ws/tests`, `ws/diff`, `ws/spec-audit`, `ws/proof`)

In the issue description:

- `SpecKey: tvm::<NAME>` / `SpecKey: fift::<ALIAS>`
- `Category:` / `Signature:` / `Short:` (from spec)
- `Encoding:` (prefix/layout metadata from spec)
- `TON ref:` (file/line/function + commit in ton-blockchain/ton)
- `Checklist:` (what “done” typically means for this instruction)

## 2) Find the relevant Lean code

Most opcode work touches `TvmLean/Core.lean` (a thin re-export), but the real definitions live in:

- `TvmLean/Core/Prelude.lean`
  - `inductive Instr` — instruction AST
  - `def Instr.pretty` — mnemonic formatting (useful for grepping and traces)
  - `def decodeCp0WithBits` / `def decodeCp0` — cp0 bitcode decoder
  - `def encodeCp0` / `def assembleCp0` — encoder/assembler helpers
- `TvmLean/Core/Exec.lean`
  - `def execInstr` — top-level semantics dispatcher
- `TvmLean/Core/Exec/<Category>/<Opcode>.lean`
  - per-opcode semantics (this is what you usually edit for “implement opcode X” work)

Tip: if the Linear issue mnemonic is `FOO`, start with `rg -n \"\\bFOO\\b\" TvmLean/Core` and/or search inside `Instr.pretty` (in `TvmLean/Core/Prelude.lean`).

## 3) Implement (typical workflow)

1. **Spec audit vs C++**
   - Use the `TON ref` commit hash to `git checkout` the exact TON version locally.
   - Read the referenced function/file and confirm the behavior (exceptions, NaN rules, edge cases).
2. **AST + decode/encode**
   - If `Instr` already has the constructor, reuse it.
   - Otherwise add a new constructor, then update `Instr.pretty`, `decodeCp0WithBits`, and `encodeCp0`.
   - Keep decode/encode symmetric; add/extend a roundtrip test in `Tests.lean` when possible.
3. **Semantics**
   - Implement the opcode in `TvmLean/Core/Exec/<Category>/<Opcode>.lean` to match TON C++ behavior (including TVM exception codes / gas rules where relevant).
4. **Tests**
   - Add a focused unit test in `Tests.lean` (use `runProg` for tiny programs when possible).
   - If the opcode is exercised in diff fixtures, run `tvm-lean-diff-test` locally and fix mismatches.

## One PR per issue

Hard rule: **close each `ws/*` subissue with exactly one PR**.

- Use the `gitBranchName` from Linear for the branch name.
- Put the Linear identifier (e.g. `TVM-5997`) in the PR title so Linear auto-links it.

## 4) Run checks

```sh
lake build
lake exe tvm-lean-tests
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures/ci --strict-exit
```

## Fift alias issues

Alias issues are about *mnemonic expansion*, not new VM behavior:

- confirm the alias maps to the correct `tvm::<actual>` per spec
- ensure any relevant pretty-printing/decoding/assembler surfaces handle it consistently
- add a small test to lock it in
