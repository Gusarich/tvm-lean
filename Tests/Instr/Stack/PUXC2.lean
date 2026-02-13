import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PUXC2

/-
INSTRUCTION: PUXC2

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path: `.puxc2` handler is selected from stack executor.
2. [B2] Dispatch miss path: non-`PUXC2` instruction must fall through to `next`.
3. [B3] Runtime underflow path: execution fails with `.stkUnd` when
   `st.stack.size <= 1` OR `x ≥ size` OR `y > size` OR `z > size`.
4. [B4] Runtime success path: with valid precondition, the engine performs
   `push(fetch x)`, `swap 0 2`, `swap 1 y`, `swap 0 z`.
5. [B5] Index-edge aliasing in success path:
   - `x = 0` (pulls top-of-stack directly),
   - `x = y`, `x = z`, and `y = z` all induce deterministic swap/fetch permutations.
6. [B6] Runtime boundary indices: boundary values at `{0,1,15}` for x/y/z and
   deep boundary `size = 16` should be exercised explicitly.
7. [B7] Assembler range handling:
   - valid params `0..15` encode to `0x544`,
   - invalid params (`>15`) throw `.rangeChk`.
8. [B8] Decoder behavior:
   - exact 24-bit opcode `0x544` decodes to `.puxc2`,
   - adjacent prefixes `0x543` and `0x545` decode as other instructions,
   - truncated bitstreams (`8`/`15` bits) trigger `.invOpcode`.
9. [B9] Gas accounting: fixed base-cost path only; exact-gas and exact-minus-one
   out-of-gas are the gas boundary branches. No variable per-argument gas penalty
   was observed.

TOTAL BRANCHES: 9

Each oracle test below is tagged [B?] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def puxc2Id : InstrId := { name := "PUXC2" }

private def refCell : Cell := Cell.empty
private def refSlice : Slice := Slice.ofCell refCell
private def refBuilder : Value := .builder Builder.empty

private def mkCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxc2Id
    program := #[.puxc2 x y z]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxc2Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseWithProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxc2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPuxc2Direct
    (x y z : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPuxc2 (.puxc2 x y z) stack

private def decodeWord (x y z : Nat) : Nat :=
  (0x544 <<< 12) + (x <<< 8) + (y <<< 4) + z

private def decodePuxc2 (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits (decodeWord x y z) 24) #[]))

private def decodeXcpu2Code (x y z : Nat) : Cell :=
  Cell.mkOrdinary (natToBits ((0x543 <<< 12) + (x <<< 8) + (y <<< 4) + z) 24) #[]

private def decodePuxcpuCode (x y z : Nat) : Cell :=
  Cell.mkOrdinary (natToBits ((0x545 <<< 12) + (x <<< 8) + (y <<< 4) + z) 24) #[]

private def rawPuxc2Trunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x54 8) #[]

private def rawPuxc2Trunc15 : Cell :=
  Cell.mkOrdinary (natToBits (0x544 >>> 1) 15) #[]

private def runGasExact : Int := computeExactGasBudget (.puxc2 0 0 0)
private def runGasExactMinusOne : Int := computeExactGasBudgetMinusOne (.puxc2 0 0 0)

private def mkIntStack (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    return out

private def idxBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 14, 15]

private def valueBoundaryPool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 17,
    intV (-17),
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    .null,
    .cell refCell,
    .slice refSlice,
    refBuilder,
    .tuple #[]
  ]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng0 : StdGen) : α × StdGen :=
  let (idx, rng1) := randNat rng0 0 (pool.size - 1)
  (pool[idx]!, rng1)

private def genStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool valueBoundaryPool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def requiredDepth (x y z : Nat) : Nat :=
  Nat.max 2 (Nat.max (x + 1) (Nat.max y z))

private def mkFuzzCase
    (base : String)
    (x y z : Nat)
    (depth : Nat)
    (rng0 : StdGen) : OracleCase × StdGen :=
  let (stack, rng1) := genStack depth rng0
  let (tag, rng2) := randNat rng1 0 999_999
  (mkCase (base ++ s!"/{tag}") x y z stack, rng2)

private def genPuxc2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    mkFuzzCase "fuzz/underflow/empty" 0 0 0 0 rng1
  else if shape = 1 then
    mkFuzzCase "fuzz/underflow/singleton" 0 0 0 1 rng1
  else if shape = 2 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let need := requiredDepth x y z
    mkFuzzCase (s!"fuzz/success/boundary/{x}-{y}-{z}") x y z (need) rng4
  else if shape = 3 then
    let (y, rng2) := pickFromPool idxBoundaryPool rng1
    let (z, rng3) := pickFromPool idxBoundaryPool rng2
    let need := requiredDepth 0 y z
    mkFuzzCase (s!"fuzz/success/x0/{y}-{z}") 0 y z (max 2 need) rng3
  else if shape = 4 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (z, rng3) := pickFromPool idxBoundaryPool rng2
    let y := x
    mkFuzzCase (s!"fuzz/success/x-eq-y/{x}-{z}") x y z (requiredDepth x y z) rng3
  else if shape = 5 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let z := x
    mkFuzzCase (s!"fuzz/success/x-eq-z/{x}-{y}") x y z (requiredDepth x y z) rng3
  else if shape = 6 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let z := y
    mkFuzzCase (s!"fuzz/success/y-eq-z/{x}-{y}") x y z (requiredDepth x y z) rng3
  else if shape = 7 then
    let (y, rng2) := pickFromPool idxBoundaryPool rng1
    let (z, rng3) := pickFromPool idxBoundaryPool rng2
    mkFuzzCase "fuzz/underflow/x-high" 15 y z 15 rng3
  else if shape = 8 then
    mkFuzzCase "fuzz/underflow/y-high" 0 15 0 2 rng1
  else if shape = 9 then
    mkFuzzCase "fuzz/underflow/z-high" 0 0 15 2 rng1
  else if shape = 10 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    mkFuzzCase "fuzz/success/non-int-heavy" x y z 8 rng4
  else
    mkFuzzCase "fuzz/success/large-depth" 7 13 2 20 rng1

def suite : InstrSuite where
  id := { name := "PUXC2" }
  unit := #[
    { name := "unit/dispatch/fallback-next"
      run := do
        -- [B2]
        expectOkStack "dispatch-fallback-to-next"
          (runHandlerDirectWithNext execInstrStackPuxc2 (.add) (VM.push (.int (.num 77))) #[])
          #[.int (.num 77)]
    }
    ,
    { name := "unit/dispatch/matched-puxc2"
      run := do
        -- [B1, B4]
        expectOkStack "matched-puxc2-basic"
          (runPuxc2Direct 0 0 0 #[intV 11, intV 22])
          #[intV 11, intV 22, intV 11]
    }
    ,
    { name := "unit/dispatch/matched-puxc2-x1"
      run := do
        -- [B1, B4, B5]
        expectOkStack "matched-puxc2-x1-y0-z1"
          (runPuxc2Direct 1 0 1 #[intV 11, intV 22])
          #[intV 22, intV 11, intV 22]
    }
    ,
    { name := "unit/underflow/empty"
      run := do
        -- [B3]
        expectErr "underflow-empty" (runPuxc2Direct 0 0 0 #[]) .stkUnd
    }
    ,
    { name := "unit/underflow/singleton"
      run := do
        -- [B3]
        expectErr "underflow-singleton" (runPuxc2Direct 0 0 0 #[intV 5]) .stkUnd
    }
    ,
    { name := "unit/underflow/x-out-of-range"
      run := do
        -- [B3]
        expectErr "underflow-x-out-of-range" (runPuxc2Direct 2 0 0 #[intV 10, intV 11]) .stkUnd
    }
    ,
    { name := "unit/underflow/y-out-of-range"
      run := do
        -- [B3]
        expectErr "underflow-y-out-of-range"
          (runPuxc2Direct 0 9 0 #[intV 10, intV 11])
          .stkUnd
    }
    ,
    { name := "unit/underflow/z-out-of-range"
      run := do
        -- [B3]
        expectErr "underflow-z-out-of-range"
          (runPuxc2Direct 0 0 9 #[intV 10, intV 11])
          .stkUnd
    }
    ,
    { name := "unit/encode/decode/assemble-valid"
      run := do
        -- [B7, B8]
        match assembleCp0 [ .puxc2 0 0 0 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble-puxc2-valid: unexpected {e}")
        match decodePuxc2 1 2 3 with
        | .ok (.puxc2 1 2 3, 24, _) => pure ()
        | .ok (i, bits, _) =>
            throw (IO.userError s!"decode-puxc2: expected .puxc2, got {i} / bits {bits}")
        | .error e =>
            throw (IO.userError s!"decode-puxc2: unexpected {e}")
    }
    ,
    { name := "unit/encode/assemble-x-invalid"
      run := do
        -- [B7]
        match assembleCp0 [ .puxc2 16 0 0 ] with
        | .ok _ => throw (IO.userError "assemble-x-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure ()
            else throw (IO.userError s!"assemble-x-invalid: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/encode/assemble-y-invalid"
      run := do
        -- [B7]
        match assembleCp0 [ .puxc2 0 16 0 ] with
        | .ok _ => throw (IO.userError "assemble-y-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure ()
            else throw (IO.userError s!"assemble-y-invalid: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/encode/assemble-z-invalid"
      run := do
        -- [B7]
        match assembleCp0 [ .puxc2 0 0 16 ] with
        | .ok _ => throw (IO.userError "assemble-z-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure ()
            else throw (IO.userError s!"assemble-z-invalid: expected rangeChk, got {e}")
    }
  ]
  oracle := #[
    -- [B2, B4]
    mkCase "ok/min-depth" 0 0 0 (mkIntStack 2)
    ,
    -- [B4, B6]
    mkCase "ok/x0-y2-z3" 0 2 3 (mkIntStack 4)
    ,
    -- [B4, B6]
    mkCase "ok/x0-y15-z0" 0 15 0 (mkIntStack 16)
    ,
    -- [B4, B6]
    mkCase "ok/x15-y14-z13" 15 14 13 (mkIntStack 16)
    ,
    -- [B4, B8]
    mkCase "ok/swap-distinct" 3 9 1 (mkIntStack 10)
    ,
    -- [B4, B5]
    mkCase "ok/x-eq-y" 5 5 2 (mkIntStack 6)
    ,
    -- [B4, B5]
    mkCase "ok/x-eq-y-non-int"
      7 7 3
      #[.null, .cell refCell, refBuilder, intV 42]
    ,
    -- [B4, B5, B8]
    mkCase "ok/x-eq-z" 9 4 9 (mkIntStack 10)
    ,
    -- [B4, B5, B8]
    mkCase "ok/x-eq-z-non-int"
      6 1 6
      #[intV 7, intV 8, .slice refSlice, .tuple #[], intV 9]
    ,
    -- [B4, B6]
    mkCase "ok/y-eq-z" 3 10 10 (mkIntStack 11)
    ,
    -- [B4, B6, B8]
    mkCase "ok/y-eq-z-non-int"
      4 11 11
      #[.null, .builder Builder.empty, intV 9, intV 10, .cell refCell]
    ,
    -- [B4, B5]
    mkCase "ok/all-equal" 7 7 7 (mkIntStack 8)
    ,
    -- [B8, B6]
    mkCase "ok/top-heavy-boundary" 1 0 15 (mkIntStack 16)
    ,
    -- [B8]
    mkCase "ok/mixed-tail-types"
      5 2 14
      #[.null, .cell refCell, .slice refSlice, refBuilder, intV 12, intV (-5), .tuple #[], intV 42]
    ,
    -- [B4, B5, B8]
    mkCase "ok/non-int-heavy-success"
      12 0 11
      #[.cont (.quit 0), .cell refCell, .null, intV 7, .slice refSlice, .tuple #[], .builder Builder.empty, intV (-3)]
    ,
    -- [B4, B6]
    mkCase "ok/high-boundary-alias" 14 10 10 (mkIntStack 16)
    ,
    -- [B3]
    mkCase "err/underflow/x-eq-y-no-headroom"
      14 14 0
      (mkIntStack 14)
    ,
    -- [B3]
    mkCase "err/underflow-empty" 0 0 0 #[]
    ,
    -- [B3]
    mkCase "err/underflow-singleton" 0 0 0 #[intV 42]
    ,
    -- [B3]
    mkCase "err/underflow-x-needs-one-more" 1 0 0 #[intV 1]
    ,
    -- [B3]
    mkCase "err/underflow-x-too-large" 3 0 0 (mkIntStack 3)
    ,
    -- [B3]
    mkCase "err/underflow-y-too-large" 0 9 0 (mkIntStack 4)
    ,
    -- [B3]
    mkCase "err/underflow-z-too-large" 0 0 9 (mkIntStack 4)
    ,
    -- [B3]
    mkCase "err/underflow-deep"
      15 15 15
      (mkIntStack 15)
    ,
    -- [B8]
    mkCaseCode "decode/round-trip"
      (mkIntStack 4)
      (Cell.mkOrdinary (natToBits (decodeWord 3 4 2) 24) #[])
    ,
    -- [B8]
    mkCaseCode "decode/neighbor-xcpu2"
      (mkIntStack 3)
      (decodeXcpu2Code 2 7 9)
    ,
    -- [B8]
    mkCaseCode "decode/neighbor-puxcpu"
      (mkIntStack 3)
      (decodePuxcpuCode 2 7 9)
    ,
    -- [B8]
    mkCaseCode "decode/truncated-8" #[] rawPuxc2Trunc8
    ,
    -- [B8]
    mkCaseCode "decode/truncated-15" #[] rawPuxc2Trunc15
    ,
    -- [B9]
    mkCaseWithProgram "gas/exact-cost-succeeds"
      (mkIntStack 2)
      #[.pushInt (.num runGasExact), .tonEnvOp .setGasLimit, .puxc2 0 0 0]
      (oracleGasLimitsExact runGasExact)
    ,
    -- [B9]
    mkCaseWithProgram "gas/exact-minus-one-fails"
      (mkIntStack 2)
      #[.pushInt (.num runGasExactMinusOne), .tonEnvOp .setGasLimit, .puxc2 0 0 0]
      (oracleGasLimitsExactMinusOne runGasExact)
  ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genPuxc2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUXC2
