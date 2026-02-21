/-
# `TvmLean.Proof` API contract

This file is the proof-layer entrypoint. Downstream proofs should import
`TvmLean.Proof` (or this file) instead of depending on internal
`TvmLean.Semantics.*` implementation details.

## Stability

- The modules re-exported below are the stable proof API surface.
- Existing names in these modules are intended to remain backwards-compatible
  (additive extensions are expected).
- Internal semantics modules outside this surface are not part of this contract.

## Module map

- `Proof.VM`: VM monad execution/projection lemmas and state-update simp facts.
- `Proof.Gas`: `GasBudget` plus lemmas for gas-side proof obligations.
- `Proof.Program`: `StepResult` accessors and program-level execution helpers.
- `Proof.Run`: `runK`/`runRaw` composition and split lemmas.
- `Proof.Invariant`: generic invariant lifting across step/run relations.
- `Proof.Stack`: typed stack views and stack-shape reasoning helpers.
- `Proof.InstrSpec`: executable instruction-spec core for supported opcodes.
- `Proof.Cell`: cell/builder/slice normalization lemmas.
- `Proof.Dict`: dictionary lookup/update rewrite lemmas.
-/

import TvmLean.Proof.VM
import TvmLean.Proof.Gas
import TvmLean.Proof.Program
import TvmLean.Proof.Run
import TvmLean.Proof.Invariant
import TvmLean.Proof.Stack
import TvmLean.Proof.InstrSpec
import TvmLean.Proof.Cell
import TvmLean.Proof.Dict
