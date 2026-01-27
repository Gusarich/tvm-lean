* TVM is a deterministic stack machine. State is stack plus control registers `c0 c1 c2 c3 c4 c5 c7`, current continuation `cc`, current codepage `cp` and gas.
* Values are tagged, no implicit conversions. Core types are Integer, Cell, Slice, Builder, Tuple, Continuation, Null.
* Integer is signed 257-bit range (-2^{256} \le x < 2^{256}) plus `NaN`. Many arithmetic ops produce `NaN` and normally also raise integer overflow, quiet variants keep going and propagate `NaN`. Using `NaN` in non quiet arithmetic or in many non arithmetic contexts triggers overflow.
* Cells are bitstrings up to 1023 bits plus up to 4 refs. Slices and builders are cursors for reading and writing. There are exotic cell types and a library context, but you can treat them as a later layer.
* Control flow is continuation based. Ordinary continuations are code slices with optional stack, savelist, codepage, nargs. There are extraordinary continuations like `Quit`, `ExcQuit`, `Repeat`, `Again`, `Until`, `WhileCondition`, `WhileBody`, `Envelope`, `PushInt`.
* Gas is part of semantics. Basic is `10 + bits of instruction prefix and fixed operands`, plus extras like `500` for finalizing a builder into a cell, cell load costs, exception cost, implicit jump and return costs.

Below is a plan that gets you something demoable early, but keeps the structure compatible with full formal verification.

## Plan overview

Build a Lean implementation in three layers, so you can ship an MVP interpreter fast and then tighten guarantees without rewriting everything:

1. **Semantic core**: instruction AST, values, VM state, and a small step function.
2. **Encoding and I/O**: decoding cp0 bitcode from a slice, and loading code and data cells from BOC if you want.
3. **Proof layer**: invariants, determinism, gas termination, and refinement theorems.

The key idea is: start by interpreting a typed instruction AST, then later prove that the decoder produces the same AST as the spec, and that stepping that AST matches the intended semantics.

## Milestone 1, MVP executable semantics that can run a real toy contract

Goal: a Lean executable that can run the “counter” style program from the docs and show final `c4`, exit code, and optionally a trace.

### 1. Define the core data model in Lean

Keep it executable first, with “well formed” as predicates, not dependent types everywhere.

* `IntVal`

  * `num : Int` plus a range predicate for 257-bit signed.
  * `nan`.
* `Value`

  * `int : IntVal`
  * `cell : Cell`
  * `slice : Slice`
  * `builder : Builder`
  * `tuple : Array Value` with length ≤ 255
  * `cont : Continuation`
  * `null`
* `Cell`

  * `bits : BitString` and `refs : Array Cell` with checks for ≤ 1023 bits and ≤ 4 refs
  * optionally `cellType` and `exotic` marker, but in MVP you can treat everything as ordinary
* `Slice`

  * `cell : Cell`, `bitPos : Nat`, `refPos : Nat`
* `Builder`

  * `bits : BitString`, `refs : Array Cell`
* `Continuation`

  * at least `Ordinary` with fields `code : Slice`, plus optional `initStack`, `savelist`, `cp`, `nargs`
  * plus the extraordinary ones you need for termination and exceptions: `Quit`, `ExcQuit`
* `Regs`

  * a small record with `c0 c1 c2 c3 c4 c5 c7` typed as `Value` but constrained by invariants
* `Gas`

  * for MVP treat as `Nat` “fuel”, but keep the record shape compatible with the real `GasLimits` from the docs, so you can swap semantics later
* `VmState`

  * `stack : List Value`
  * `regs : Regs`
  * `cc : Continuation`
  * `cp : Nat` or a small enum, start with `0`
  * `gas : Gas`

Design choice that pays off later: put *all failure modes* through a single mechanism “throw exception code and jump to `c2`”, because that is how TVM actually behaves. That avoids a split between “errors” and “control flow”.

### 2. Instruction AST for the MVP subset

Define an `Instr` inductive type for the subset needed to run a minimal contract.

For the counter example from your docs, you need roughly:

* codepage and flow: `SETCP0`, `IFRET`
* stack basics: `PUSH s[i]`, `POP s[i]`, `XCHG`, maybe `SWAP`, `DUP`, `TUCK`
* registers: `PUSHCTR c4`, `POPCTR c4` at least
* slice builder basics: `CTOS`, `NEWC`, `LDU n`, `STU n`, `ENDS`, `ENDC`
* int ops: `INC`, `EQUAL`
* exceptions: `THROWIFNOT code`

That is enough to demo a meaningful state change in `c4`.

### 3. Small step semantics as a total function

Write a pure step function that is easy to reason about:

* `step : VmState → StepResult`

Where `StepResult` is something like:

* `continue st`
* `halt exitCode st`

In TVM terms, “halt” happens by invoking `Quit`, and “exceptions” happen by switching `cc` to `c2` after pushing an exception code on the stack and charging exception gas. In MVP you can implement `ExcQuit` as a special continuation that pops the code and halts.

Important helpers:

* `pop1`, `pop2`, `push` with stack underflow detection producing exception code 2.
* `expectInt`, `expectSlice`, `expectBuilder`, `expectCell`, with type check error code 7.
* `checkNaN` behavior for the specific instruction. Example: `IFRET` must throw integer overflow if the flag is `NaN` as described in `tvm.tex`.
* `rangeCheck` for serialization instructions like `STU n`, that is exit code 5 if the integer does not fit, matching `tvm.tex` for `STU` and friends.

For the MVP, you can model `cc` as “current list of Instr” rather than a slice, to avoid decoding. You still keep the `Continuation` type, but `Ordinary` holds `List Instr` for now.

That gives you a runnable interpreter quickly and you can already validate tricky behaviors: NaN handling, exit codes, stack discipline, slice bounds.

### 4. Demo harness

Add a tiny CLI style entrypoint that:

* constructs an initial state matching “internal message” style stack shape from the MDX doc, but you can keep it minimal
* runs the program
* prints exit code, final stack, `c4` cell bits, maybe `c5`

This is enough to demo “Lean reference VM executes a real looking TVM assembly program deterministically and updates storage”.

## Milestone 2, make it run real TVM bytecode, still with partial opcode support

Goal: feed it real code cells produced by existing tooling, without changing the semantic core.

### 1. Introduce a decoder boundary

Keep the semantic evaluator working over `Instr`. Add:

* `decodeCp0 : Slice → Except DecodeError (Instr × Slice)`
* `fetch : VmState → Except Error (Instr × VmState)`

  * reads next instruction from `cc` which is now a slice
  * handles end of code and implicit jump or implicit return rules

Then `step` becomes:

* decode one instruction according to `cp`
* execute semantics for that instruction

This is also where you encode “invalid opcode” as exception code 6.

### 2. Implement only the cp0 encodings you need first

For MVP bytecode support, implement the exact prefixes for your subset only. You can pull them from:

* `tvm.tex` opcode appendix, plus
* the MDX instruction table listing opcodes and mnemonics.

Do not start by supporting everything, just enough to decode and run one compiled example.

### 3. BOC and cell serialization as optional, untrusted input layer

To demo against real contracts, you likely want to load BOC.

You can choose one of two trust profiles:

* **Fast path**: parse BOC in Lean but treat the parser as “engineering code”, not formally verified yet. The verified thing is still the VM semantics once you have a `Cell`.
* **Hard path later**: prove your BOC parser correct against the TON cell serialization spec.

For an MVP demo, the fast path is fine and still credible.

## Milestone 3, grow instruction coverage along realistic contract needs

Goal: execute typical on chain contracts, not just toy examples.

Do it as vertical slices, not instruction categories.

### Slice A: “real world compute phase core”

* full stack primitives and compound stack ops
* arithmetic core with NaN and quiet prefix `QUIET` from `tvm.tex`
* comparisons, including quiet comparisons that return `NaN` for ternary logic
* full exception and TRY mechanism with `c2` handling and exception stack effects
* full continuation manipulation for calls and jumps: `CALLREF`, `JMPREF`, `RET`, implicit return behavior and `c0` chaining as in the continuations doc

### Slice B: “cells as a first class persistent format”

* more builder and slice ops, refs ops, endian variants used by compilers
* enforce 1023 bits and 4 refs limits precisely, throw the correct “cell overflow” or “cell underflow” exit codes
* start modeling exotic cells enough to not crash on common ones, you can still treat complex loading rules as “unsupported” with a clear exception until you implement them

### Slice C: “hashmaps and dictionaries”

This is a big domain specific chunk and very worth putting behind a dedicated module because it is both error prone and security critical.

* model TON Hashmap operations as per spec, including key length, fork nodes, and the exact failure modes
* implement DICT instructions used by real toolchains, especially the combined ones like `DICTIGETJMP` patterns described in the registers doc for `c3`

### Slice D: “environment and crypto”

* `c7` environment tuple fields, but as explicit inputs, never “read host time”
* crypto instructions, either using a pure Lean implementation or an explicitly declared trust boundary with test vectors

## Milestone 4, formal verification that scales

Goal: the Lean VM is not just executable, it comes with proofs that it matches the spec and cannot “go wrong” except by throwing the specified TVM exceptions.

### 1. Define well formedness predicates

Do not encode everything as dependent types at first. Use predicates and prove preservation.

Examples:

* `WF_Int` enforces the 257-bit bound for `num`.
* `WF_Cell` enforces ≤ 1023 bits, ≤ 4 refs, plus exotic constraints when you add them.
* `WF_Slice` ensures positions are in bounds.
* `WF_Builder` ensures bounds.
* `WF_Tuple` ensures length ≤ 255 and all components are WF.
* `WF_State` glues stack, regs, cc, cp, gas.

### 2. Prove the “boring but essential” global theorems early

They stay valid as you add instructions.

* Determinism: `step` is a function, so trivial, but also prove a relational version if you later introduce an inductive small step relation.
* Progress style statement: if `WF_State st`, then `step st` either continues with `WF_State st'` or takes the VM into the exception handler in a spec compliant way or halts with `Quit`.
* Gas monotonicity: for the instructions you support, prove that gas decreases by at least the required amount, this gives you a termination measure for `run` based on `gas_remaining`.

### 3. Instruction local lemmas, generated and structured

To avoid proof hell with hundreds of opcodes, keep a uniform template:

* one lemma per instruction describing stack effect and the postcondition
* proofs are mostly rewriting plus bounds checks

This is where code generation helps a lot.

### 4. Refinement story, so you can change representations without re proving semantics

You will likely switch representations for performance or simplicity, for example `List Bool` to `ByteArray` bits.

Use a refinement relation:

* `R_Value`, `R_Cell`, `R_State`

Then prove:

* executing with representation A refines executing with representation B

That gives you freedom to optimize the runnable reference without losing proofs.

## Engineering tactics to keep it sane

### Use code generation for opcode plumbing

The instruction set is too large to hand write without mistakes.

Use a script to parse your MDX `instructions.mdx` static section and emit:

* `Instr` constructors
* decode patterns for cp0 prefixes
* a semantics stub file that fails with “unimplemented” per instruction until you fill it

The semantics of each instruction still lives in Lean, but the boilerplate is generated.

### Differential testing against the existing C++ VM

Even with formal proofs, you need coverage against “what the chain does today”.

* build a test harness that runs the same code and initial state in C++ and Lean
* compare exit code, final stack prefix, `c4`, `c5`, gas used and thrown exception codes
* include randomized small programs for the subset you have implemented to catch corner cases like NaN propagation and slice bounds

This also helps you detect places where `tvm.tex` and current behavior diverge.

### Keep a spec index

Create a small table in the repo mapping each implemented instruction to:

* `tvm.tex` point reference or opcode appendix entry
* MDX entry name and opcode
* any known divergence note and a test demonstrating it

This becomes the “proper specification” you currently lack.

## What you can demo quickly with this approach

* A Lean executable that runs a small cp0 program that uses cells, slices, builders, `c4` storage update, and exception handling.
* A trace that shows stack and register evolution, which is immediately useful for debugging C++ divergence.
* A first proof bundle that is meaningful but not huge:

  * determinism
  * preservation of basic well formedness for the supported subset
  * gas decreases and `run` terminates under a gas bound

After that, extending is mostly “add instructions and prove their local lemma”, not “rethink the architecture”.
