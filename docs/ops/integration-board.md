# Integration Board (WS-00)

As-of: 2026-02-21

## Ownership map and conflict policy

- Shared files (`PLAN.md`, `Contracts.lean`, `docs/development/*`) are merged only during integration windows.
- Workstream owners avoid touching other workstream-owned files unless explicitly coordinating a handoff.
- Conflict rule: if another lane already changed a file, prefer adding helper APIs in your own lane and defer shared-file edits to integration.

## Package state board

| Package | State | Notes |
| --- | --- | --- |
| Pack A (WS-01) | done | Proof API hardening merged |
| Pack B (WS-02/03) | done | Gas + decode bridge merged |
| Pack C (WS-05) | done | Stack/arith spec layer merged |
| Pack D (WS-06) | done | Cell/slice proof helpers merged |
| Pack E (WS-07) | done | Flow/control wrappers merged |
| Pack F (WS-08) | done | Dict proof toolkit merged |
| Pack G (WS-09) | done | Invariant framework + loop example merged |
| Pack H (WS-10) | done | Contract examples merged |
| Pack I (WS-11) | done | Scaffold tool v2 merged |
| Pack J (WS-12/13) | done | Validation/docs hardening merged |
| Pack K (WS-14) | done | Final integration + stabilization merged |

## Dependency board

| Dependency | Status | Notes |
| --- | --- | --- |
| WS-01 before WS-10 proof ergonomics | satisfied | Stable proof entrypoint and wrappers in place |
| WS-02/03 before bytecode-heavy proofs | satisfied | Gas + decode bridges in place |
| WS-05/06/07 before broad contract proving | satisfied | Instruction-spec bridges in place |
| WS-08 before dict-centric contracts | satisfied | Dict postcondition toolkit in place |
| WS-09 before loop-heavy contracts | satisfied | Invariant helpers and loop example in place |
| WS-11/12/13 before handoff | satisfied | Scaffold + docs + validation matrix in place |

## Unblocked queue

- None. All listed packs are in `done` state.
