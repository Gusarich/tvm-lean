# Writing Proofs for VM Execution

This guide describes the proof-facing API for `TvmLean/Semantics/Step/*` and the patterns that keep long execution proofs short, stable, and fast to elaborate.

## Which runner to use

- `VmState.runK host fuel st`:
  - Returns `Sum (Int × VmState) VmState`.
  - `Sum.inl (exitCode, st')`: halted before fuel was exhausted.
  - `Sum.inr st'`: fuel exhausted while still continuing.
  - Best when proving prefix/suffix composition (`runK_add`) or when you need intermediate states.

- `VmState.runRaw host fuel st`:
  - Returns `StepResult`.
  - Wraps `runK`; if fuel is exhausted it returns `.halt Excno.fatal.toInt st'`.
  - Best for “exactly this fuel budget yields this raw halt/fatal result”.

- `VmState.run host fuel st`:
  - Finalized runner (`-1/-2` commit handling via `finalizeHalt`).
  - Best for top-level VM behavior claims.

## Core proof API

From `TvmLean/Semantics/Step/Proof.lean`:

- Relational semantics:
  - `StepN` (`st -[host, n]-> st'`) for `n` continue steps.
  - `StepHaltN` (`st -[host, n]->halt (exit, st')`) for halt after `n` total steps.
- Bridges:
  - `stepN_to_runK`, `stepN_to_runRaw`, `stepHaltN_to_runRaw`.
  - `runK_inr_to_stepN`, `runK_inl_to_stepHaltN`.
- Determinism:
  - `stepN_deterministic`, `stepHaltN_deterministic`.
- Scripted execution:
  - `RunScript`, `runK_of_script`.
  - `runRaw_of_script_halt`, `runRaw_of_script_continue`.
  - `run_of_script_halt`, `run_of_script_continue`.
- Decode/step factoring:
  - `stepOrdinaryDecode_cp0_of_decode_ok`.
  - `stepOrdinaryDecode_cp0_of_decode_error`.
  - `stepOrdinaryDecode_nonCp0`.

## Controlled unfolding pattern

Avoid `simp [VmState.run]` on large traces. Prefer:

1. One-step rewrite lemmas (`runRaw_succ`, `VmState.run_succ_finalized`, or script theorems).
2. Step evaluation lemmas (`stepN_eval`) that prove one concrete transition.
3. Reuse script/bridge lemmas instead of repeatedly unfolding recursion.

Use `vm_simp` (defined in `Step/Proof.lean`) for the safe subset of runner simplifications.

## Structuring step-eval lemmas

For a concrete step theorem, keep this shape:

1. Precompute gas side-conditions (`decide (... < 0) = false`).
2. Reduce `VmState.step` to the relevant continuation case.
3. Reduce `VmState.stepOrdinary` to `stepOrdinaryDecode`.
4. Discharge decode with a small decode lemma.
5. Conclude with `stepOrdinaryOk`/`stepOrdinaryInvalid`.

This keeps each lemma local and avoids global unfolding cascades.

## Keep proof terms small

- Keep heavyweight defs locally irreducible when not needed (`execInstr`, large code constants, broad decoders).
- Isolate arithmetic side-conditions in named lemmas; do not inline large normalization terms repeatedly.
- Prefer theorem boundaries over giant `simp` calls spanning many definitions.

## Cookbook patterns

### 1) Execute `N` steps and prove final state

- Build a `RunScript host N st0 (Sum.inl (exit, stN))`.
- Finish with:
  - `runRaw_of_script_halt` for raw runner, or
  - `run_of_script_halt` for finalized runner.

### 2) Prove an invariant across `N` steps

- Prove a one-step preservation lemma over `StepContinue`.
- Lift with induction on `StepN`.
- Optionally bridge from `runK` using `runK_inr_to_stepN`.

### 3) Prove decode for an assembled snippet

- Use focused stage helpers in `Cp0` (`decodeCp0_a9_fixed16`, `decodeCp0_q_a9_24`, stage decoders).
- State exact decode lemma for the snippet once.
- Reuse it through `stepOrdinaryDecode_cp0_of_decode_ok`.

## Useful local checks

- Proof file:
  - `lake env lean Proofs/ToyCounter.lean`
- Core semantics:
  - `lake build TvmLean.Semantics`
- Model/decode changes:
  - `lake build TvmLean.Model.Instr.Codepage.Cp0`
