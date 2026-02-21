# Writing Proofs for VM Execution

This guide covers the proof-facing API around `TvmLean/Semantics/Step/*` and the proof patterns that keep execution theorems small, stable, and quick to elaborate.

## Workflow quickstart

Use this sequence for a new contract proof:

1. Import `TvmLean.Proof` plus your contract `Program`/`Spec` modules.
2. Define one canonical `initState` and small runner wrappers (`execProgram`, optional decoded-bytecode runner).
3. Pick the runner shape up front (`runK`, `runRaw`, or finalized `run`) and keep theorem statements consistent with that choice.
4. Prove one decode/assembly bridge lemma once (for bytecode-backed workflows), then reuse it everywhere.
5. Build execution results via `RunScript` + `vm_step` / `vm_halt` or compact one-step lemmas.
6. Export user-facing postcondition theorems in spec vocabulary (`Post`, `PostLookup`, etc.), not interpreter internals.
7. Spot-check compile time early with `lake env lean Contracts/<Name>/Proof.lean`.

## Proof kit import

Use the proof kit entrypoint:

- `import TvmLean.Proof`

`TvmLean.Proof` re-exports the modules in `TvmLean/Proof/README.lean`.

## Module cheat-sheet

| Module | Reach for it when | Typical helpers |
|---|---|---|
| `TvmLean/Proof/VM.lean` | Rewriting VM monad/state projections | VM state projection lemmas, runner projection rewrites |
| `TvmLean/Proof/Gas.lean` | Isolating gas side conditions | Gas arithmetic and non-negative guard helpers |
| `TvmLean/Proof/Program.lean` | Bridging program/bytecode runners | `VmState.execProgram`, decode/execute bridge lemmas |
| `TvmLean/Proof/Run.lean` | Building step-by-step traces | `RunScript`, `vm_step`, `vm_halt`, script-to-run bridges |
| `TvmLean/Proof/Invariant.lean` | Reusing invariant templates across runs | `Inv`, `InvStep`, `runK_inv`, `runK_split_inv` |
| `TvmLean/Proof/Stack.lean` | Avoiding raw stack indexing | `TypedVal`, `StackView`, typed stack extraction |
| `TvmLean/Proof/InstrSpec.lean` | Proving single-instruction behavior | Instruction-spec bridge lemmas (e.g. control-flow op specs) |
| `TvmLean/Proof/Cell.lean` | Proving cell/slice facts | Cell/slice helper lemmas for state/data proofs |
| `TvmLean/Proof/Dict.lean` | Proving dictionary postconditions | Reusable dictionary lookup/update/delete lemmas |

## Which runner to use

- `VmState.runK host fuel st`
  - Returns `Sum (Int × VmState) VmState`.
  - `Sum.inl (exitCode, st')` means halt before fuel exhaustion.
  - `Sum.inr st'` means fuel exhaustion while still continuing.
  - Best for prefix/suffix composition (`runK_add`) and intermediate-state arguments.
- `VmState.runRaw host fuel st`
  - Returns `StepResult`.
  - Wraps `runK`; fuel exhaustion is reported as `.halt Excno.fatal.toInt st'`.
  - Best when you want exact raw halt/fatal outcomes at a fixed fuel budget.
- `VmState.run host fuel st`
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

Avoid `simp [VmState.run]` on long traces. Prefer:

1. One-step rewrite lemmas (`runRaw_succ`, `VmState.run_succ_finalized`, or script bridges).
2. Step evaluation lemmas (`stepN_eval`) for concrete transitions.
3. Reusing script/bridge lemmas instead of repeatedly unfolding recursion.

Use `vm_simp` for the safe runner simplification subset, and build scripts incrementally with `vm_step h` / `vm_halt h`.

## Structuring step-eval lemmas

For a concrete step theorem:

1. Precompute gas side conditions (`decide (... < 0) = false`).
2. Reduce `VmState.step` to the relevant continuation branch.
3. Reduce `VmState.stepOrdinary` to `stepOrdinaryDecode`.
4. Discharge decode with a small dedicated decode lemma.
5. Conclude with `stepOrdinaryOk` or `stepOrdinaryInvalid`.

This keeps each lemma local and avoids global unfolding cascades.

## Keep proof terms small

- Keep heavyweight defs locally irreducible when unnecessary (`execInstr`, large code constants, broad decoders).
- Isolate arithmetic side conditions in named lemmas.
- Prefer theorem boundaries over giant cross-module `simp` calls.

## Flow/control spec usage

Use this for branch/continuation instructions (`IF`, conditional exits, continuation ops):

1. Prove gas side conditions once (usually a tiny `native_decide` lemma).
2. Rewrite the runner shell (`VmState.execProgram_single`, `VmState.execProgramStep_unfold`).
3. Replace opcode behavior with the matching `InstrSpec` run lemma (`execInstrSpecCore`, `instrSpec_*_run*`).
4. Close the goal with targeted `simp` on the consumed-state expression.

Reference: `Contracts/FlowGate/Proof.lean`.

## Loop/invariant workflow

Use this for bounded loops or repeated micro-steps:

1. Define `Inv : VmState → Prop` on the loop boundary state.
2. Prove one-step preservation over `StepContinue`.
3. Lift it with `stepN_lift_invariant` (or directly `runK_inr_lift_invariant`).
4. Bridge executable runs with `runK_inr_to_stepN` / `runK_inl_to_stepHaltN`; use `runK_add` when splitting fuel prefixes/suffixes.

## VM script macro cookbook (`vm_*`)

Use these tactics when constructing `RunScript` witnesses:

| Macro | Use it for | Input shape |
|---|---|---|
| `vm_step h` | Add one continue transition | `h : VmState.step host stᵢ = .continue stᵢ₊₁` |
| `vm_halt h` | Finish with halt transition | `h : VmState.step host stᵢ = .halt exit stᵢ₊₁` |
| `vm_script [h₁, …, hₙ]` | Full script ending in halt | `h₁..hₙ₋₁` continue, `hₙ` halt |
| `vm_script_cont [h₁, …, hₙ]` | Continue-only prefix script | all lemmas are continue transitions |
| `vm_done` | Close an empty tail (`fuel = 0`) | no lemma needed |

Companion helpers: `vm_step_assumption`, `vm_halt_assumption`, `vm_branch`, `vm_branch_assumption`.

Minimal patterns:

```lean
have hscript : RunScript host 3 st0 (Sum.inl (exitCode, st3)) := by
  vm_script [h01, h12, h23]
```

```lean
have hprefix : RunScript host 2 st0 (Sum.inr st2) := by
  vm_script_cont [h01, h12]
```

Then bridge to runner claims with `runK_of_script`, `runRaw_of_script_halt`/`runRaw_of_script_continue`, or `run_of_script_halt`/`run_of_script_continue`.

## Cookbook patterns

### 1) Straight-line instruction program pattern

Use for fixed instruction lists with no branching uncertainty.

- Build a `RunScript host N st0 (Sum.inl (exit, stN))`.
- Assemble the script with `vm_step`/`vm_halt`.
- Bridge to executable runners via `runRaw_of_script_halt` or `run_of_script_halt`.
- Reference: `TvmLean/Proof/Examples/ToyCounterTrace.lean`.

### 2) Bytecode bridge pattern

Use when proving both assembled-program and decoded-bytecode entrypoints.

- Prove `assembleDecodeMatches decodeFuel program = true`.
- State one bridge theorem from decoded execution to `execProgram`.
- Reuse that theorem in all higher-level spec proofs.
- Reference: `Contracts/ToyCounter/Proof.lean`.

### 3) Dictionary postcondition pattern

Use for dictionary-heavy contracts and state APIs.

- Prove tiny base lemmas first (`lookup_empty_none`, `delete_empty_none`, etc.).
- Wrap them into spec-facing predicates (`PostLookup`, `PostDelete`).
- Keep dictionary trace/value details inside helper lemmas, not top-level theorem statements.
- Reference: `Contracts/DictCounter/Proof.lean`.

## Anti-patterns to avoid

- Unfolding `VmState.run`/`VmState.step` globally with broad `simp` on long traces.
- Re-proving identical decode facts inline in multiple theorems.
- Mixing finalized (`run`) and raw (`runRaw`) conclusions in one theorem statement.
- Leaving arithmetic/gas side-conditions anonymous inside large proof terms.
- Exposing low-level stack/register internals in top-level spec theorems.

## Troubleshooting quick map

| Symptom | Usually means | First fix to try |
|---|---|---|
| Goal is stuck on `decide (... < 0)` | Gas side condition not isolated | Add a named helper lemma and discharge it early (often with `native_decide`) |
| `runK` result shape mismatches (`inr` vs `inl`) | Fuel/result shape is under-specified | State exact fuel budget and bridge through `runK_inr_to_stepN` / `runK_inl_to_stepHaltN` |
| `simp` explodes or times out | Too many reducible heavy defs | Mark heavy defs locally irreducible and rewrite through small step lemmas |
| Script proof cannot close final state | Missing one-step transition witness | Add a focused step lemma and feed it via `vm_step` / `vm_halt` |
| Finalized result mismatches raw exit code | `run` applies halt finalization | Prove in `runRaw` first, then map to `run` with finalize-aware lemma |

## Useful local checks

- Contract proof file:
  - `lake env lean Contracts/ToyCounter/Proof.lean`
- Core semantics:
  - `lake build TvmLeanSemantics`
- Decode/model changes:
  - `lake build TvmLeanModel`

## Contract scaffold generator

Use `tools/gen_contract_scaffold.py`:

```sh
tools/gen_contract_scaffold.py MyContract
tools/gen_contract_scaffold.py MyContract --overwrite
```

Generated files:

- `Contracts/MyContract/Program.lean`
- `Contracts/MyContract/Spec.lean`
- `Contracts/MyContract/Proof.lean`

## Reference contract proofs

- `Contracts/ToyCounter/Proof.lean`: instruction-list workflow plus bytecode bridge checks.
- `Contracts/DictCounter/Proof.lean`: reusable dictionary postcondition lemmas on empty state.
- `Contracts/FlowGate/Proof.lean`: control-flow (`IF`) proof via instruction-spec lemmas.
- `Contracts/MsgParser/Proof.lean`: parser/postcondition checks written as short spec lemmas.
- `Contracts/NonceGuard/Proof.lean`: nonce acceptance/replay guard postconditions.
- `Contracts/LoopCounter/Proof.lean`: bounded-loop invariant pattern and postcondition closure.
