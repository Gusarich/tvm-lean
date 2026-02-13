import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PUXCPU

/-
INSTRUCTION: PUXCPU

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path: matched `.puxcpu` executes `execInstrStackPuxcpu`; otherwise control passes through to `next`.
2. [B2] Runtime normal path: for valid stack depth `x < depth` and `y ≤ depth` and `z ≤ depth`, `fetch x`, `push`, `swap 0 1`, `swap 0 y`, `fetch z`, `push` are executed.
3. [B3] Runtime underflow branch for `x`: when `x >= depth`, first guard `check_underflow_p(x)` fails and instruction throws `.stkUnd` before any mutation.
4. [B4] Runtime underflow branch for `y`: with valid `x` and `x < depth`, `y > depth` still triggers `.stkUnd` after the initial `push`.
5. [B5] Runtime underflow branch for `z`: with valid `x` and `y`, `z > depth` triggers `.stkUnd` when second fetch is attempted.
6. [B6] Index edge behavior: `x = 0` makes the first `swap 0 1` no-op in effect before aliasing effects from `swap 0 y`.
7. [B7] Permutation edge behavior: index aliasing (`x = y`, `x = z`, `y = z`, all equal) yields different stack outcomes and must be exercised.
8. [B8] Assembler encoding boundaries: `.puxcpu x y z` accepts each of `x,y,z` in `0..15`, encoded as 24 bits.
9. [B9] Assembler rejection boundaries: any argument above `15` must throw `.rangeChk`.
10. [B10] Decoder opcode boundaries: decode `0x545` with packed args as `.puxcpu` and exactly 24 bits.
11. [B11] Decoder adjacency: neighboring `0x544` and `0x546` decode as different stack instructions, not `PUXCPU`.
12. [B12] Decoder truncation: 8-bit and 15-bit streams are not enough for `.puxcpu` decoding and must fail with `.invOpcode`.
13. [B13] Gas edge case: fixed path `gasPerInstr + bits`; exact budget succeeds and exact-minus-one fails.

TOTAL BRANCHES: 13

Assembler category: valid and rejection branches are explicit; there is no variable gas penalty branch
besides fixed cost with exact and exact-minus-one checks.
-/

private def puxcpuId : InstrId := { name := "PUXCPU" }

private def dispatchSentinel : Int := 1337

private def refCell : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def baseSlice : Slice := Slice.ofCell refCell

private def makeStack (n : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:n] do
    out := out.push (intV (Int.ofNat i))
  return out

private def mkCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxcpuId
    program := #[.puxcpu x y z]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxcpuId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runPuxcpuDirect (x y z : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPuxcpu (.puxcpu x y z) stack

private def runPuxcpuFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPuxcpu instr (VM.push (intV dispatchSentinel)) stack

private def wordPuxcpu (x y z : Nat) : Nat :=
  (0x545 <<< 12) + (x <<< 8) + (y <<< 4) + z

private def decodePuxcpu (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits (wordPuxcpu x y z) 24) #[]))

private def decodePuxc2 (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits
    (Slice.ofCell (Cell.mkOrdinary (natToBits ((0x544 <<< 12) + (x <<< 8) + (y <<< 4) + z) 24) #[]))

private def decodePu2xc (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits
    (Slice.ofCell (Cell.mkOrdinary (natToBits ((0x546 <<< 12) + (x <<< 8) + (y <<< 4) + z) 24) #[]))

private def puxcpuRawCode : Cell :=
  Cell.mkOrdinary (natToBits (wordPuxcpu 3 4 5) 24) #[]

private def puxc2RawCode : Cell :=
  Cell.mkOrdinary (natToBits ((0x544 <<< 12) + (2 <<< 8) + (1 <<< 4) + 7) 24) #[]

private def pu2xcRawCode : Cell :=
  Cell.mkOrdinary (natToBits ((0x546 <<< 12) + (8 <<< 8) + (9 <<< 4) + 15) 24) #[]

private def truncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0x54 8) #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0x545345 >>> 1) 15) #[]

private def nonIntPool : Array Value :=
  #[
    .null,
    .cell refCell,
    .slice baseSlice,
    .builder Builder.empty,
    .tuple #[]
  ]

private def idxBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 14, 15]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng0 : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng0 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut rng := rng0
    let mut out : Array Value := #[]
    for _ in [0:count] do
      let (shapeRaw, rng') := randNat rng 0 99
      rng := rng'
      let shape : Nat := if shapeRaw % 5 = 0 then 1 else 0
      if shape = 1 then
        let (v, rng') := pickFromPool nonIntPool rng
        out := out.push v
        rng := rng'
      else
        let n := Int.toNat (Int.ofNat (out.size + 1) % 16)
        out := out.push (intV (Int.ofNat n))
    return (out, rng)

private def mkFuzzCase
    (baseName : String)
    (x y z : Nat)
    (depth : Nat)
    (rng0 : StdGen) : OracleCase × StdGen :=
  let (stack, rng1) := genStack depth rng0
  let (tag, rng2) := randNat rng1 0 999_999
  ({ name := s!"{baseName}/{tag}", instr := puxcpuId, program := #[.puxcpu x y z], initStack := stack }, rng2)

private def genPuxcpuFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (depth, rng2) := randNat rng1 1 8
    let maxX := depth - 1
    let (x, rng3) := randNat rng2 0 maxX
    let (y, rng4) := randNat rng3 0 depth
    let (z, rng5) := randNat rng4 0 depth
    let (tag, rng6) := randNat rng5 0 999_999
    (mkCase (s!"fuzz/success/near-boundary/{tag}") x y z (makeStack (depth + 1)), rng6)
  else if shape = 1 then
    let (depth, rng2) := randNat rng1 3 14
    mkFuzzCase (s!"fuzz/success/x0-boundary-yz") 0 depth depth depth rng2
  else if shape = 2 then
    let (depth, rng2) := randNat rng1 2 12
    let xVal : Nat := depth - 1
    mkFuzzCase (s!"fuzz/success/alias-x-y") xVal xVal 3 (depth + 1) rng2
  else if shape = 3 then
    let (depth, rng2) := randNat rng1 2 12
    let xVal : Nat := if depth > 1 then depth - 2 else 0
    mkFuzzCase (s!"fuzz/success/alias-x-z") xVal 2 xVal (depth + 1) rng2
  else if shape = 4 then
    let (depth, rng2) := randNat rng1 2 12
    let yVal : Nat := depth - 1
    mkFuzzCase (s!"fuzz/success/alias-y-z") 0 yVal yVal (depth + 1) rng2
  else if shape = 5 then
    let (depth, rng2) := randNat rng1 4 16
    mkFuzzCase (s!"fuzz/success/edge-max-stack") 15 (depth - 1) (depth - 1) depth rng2
  else if shape = 6 then
    let (depth, rng2) := randNat rng1 0 15
    let (x, rng3) :=
      if depth = 15 then
        (15, rng2)
      else if depth = 0 then
        (1, (let (_, rng') := randNat rng2 1 2; rng'))
      else
        let (delta, rng') := randNat rng2 1 2
        (depth + delta, rng')
    let (_y, rng4) := pickFromPool idxBoundaryPool rng3
    let (_z, rng5) := pickFromPool idxBoundaryPool rng4
    let name := s!"fuzz/underflow/x/{x}"
    mkFuzzCase name 16 0 0 (depth + 1) rng5
  else if shape = 7 then
    let (depth, rng2) := randNat rng1 1 14
    let x : Nat := if depth = 0 then 0 else depth - 1
    let y : Nat :=
      let over := depth + 1
      if over > 15 then 15 else over
    mkFuzzCase (s!"fuzz/underflow/y/{y}") x y 0 (depth + 1) rng2
  else if shape = 8 then
    let (depth, rng2) := randNat rng1 1 14
    let x : Nat := if depth = 0 then 0 else depth - 1
    let z : Nat :=
      let over := depth + 1
      if over > 15 then 15 else over
    mkFuzzCase (s!"fuzz/underflow/z/{z}") x 0 z (depth + 1) rng2
  else if shape = 9 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"fuzz/decode/raw-puxcpu/{tag}", instr := puxcpuId, codeCell? := some puxcpuRawCode, initStack := makeStack 4 }, rng2)
  else if shape = 10 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"fuzz/decode/neighbor-544/{tag}", instr := puxcpuId, codeCell? := some puxc2RawCode, initStack := makeStack 2 }, rng2)
  else if shape = 11 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"fuzz/decode/neighbor-546/{tag}", instr := puxcpuId, codeCell? := some pu2xcRawCode, initStack := makeStack 2 }, rng2)
  else if shape = 12 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"fuzz/decode/truncated-8/{tag}", instr := puxcpuId, codeCell? := some truncated8Code, initStack := #[] }, rng2)
  else if shape = 13 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"fuzz/decode/truncated-15/{tag}", instr := puxcpuId, codeCell? := some truncated15Code, initStack := #[] }, rng2)
  else
    let budget := computeExactGasBudget (.puxcpu 0 0 0)
    let budgetMinus := computeExactGasBudgetMinusOne (.puxcpu 0 0 0)
    if shape = 14 then
      let (tag, rng2) := randNat rng1 0 999_999
      ({ name := s!"fuzz/gas/exact/{tag}", instr := puxcpuId, initStack := makeStack 1, gasLimits := oracleGasLimitsExact budget }, rng2)
    else if shape = 15 then
      let (tag, rng2) := randNat rng1 0 999_999
      ({ name := s!"fuzz/gas/exact-minus-one/{tag}", instr := puxcpuId, initStack := makeStack 1, gasLimits := oracleGasLimitsExactMinusOne budgetMinus }, rng2)
    else
      mkFuzzCase "fuzz/success/non-int-heavy" 0 1 2 8 rng1

private def gasExact : Int := computeExactGasBudget (.puxcpu 0 0 0)
private def gasExactMinusOne : Int := computeExactGasBudgetMinusOne (.puxcpu 0 0 0)

def suite : InstrSuite where
  id := puxcpuId
  unit := #[
    { name := "unit/dispatch/fallback-next"
      run := do
        -- [B1]
        expectOkStack "dispatch-fallback-add"
          (runPuxcpuFallback .add (#[intV 1, intV 2]))
          (#[] |>.push (intV 1) |>.push (intV 2) |>.push (intV dispatchSentinel))
    }
    ,
    { name := "unit/dispatch/matched"
      run := do
        -- [B2]
        expectOkStack "dispatch-matched"
          (runPuxcpuDirect 0 0 0 (#[intV 1, intV 2]))
          (#[] |>.push (intV 1) |>.push (intV 2) |>.push (intV 2) |>.push (intV 2))
    }
    ,
    { name := "unit/runtime/normal-small"
      run := do
        -- [B2]
        expectOkStack "normal-small"
          (runPuxcpuDirect 1 1 0 (#[intV 11, intV 22, intV 33]))
          (#[intV 11, intV 22, intV 22, intV 33, intV 33])
    }
    ,
    { name := "unit/runtime/noop-x-boundary"
      run := do
        -- [B6]
        expectOkStack "x-zero-boundary"
          (runPuxcpuDirect 0 2 0 (#[intV 5, intV 6, intV 7]))
          (#[intV 5, intV 7, intV 6, intV 6])
    }
    ,
    { name := "unit/runtime/underflow-x"
      run := do
        -- [B3]
        expectErr "underflow-x" (runPuxcpuDirect 3 0 0 (#[intV 11])) .stkUnd
    }
    ,
    { name := "unit/runtime/underflow-y"
      run := do
        -- [B4]
        expectErr "underflow-y" (runPuxcpuDirect 0 3 0 (#[intV 1, intV 2])) .stkUnd
    }
    ,
    { name := "unit/runtime/underflow-z"
      run := do
        -- [B5]
        expectErr "underflow-z" (runPuxcpuDirect 0 1 3 (#[intV 1, intV 2])) .stkUnd
    }
    ,
    { name := "unit/assemble/valid-boundary"
      run := do
        -- [B8]
        match assembleCp0 [ .puxcpu 0 0 0 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble-valid failed: {e}")
    }
    ,
    { name := "unit/assemble/valid-max"
      run := do
        -- [B8]
        match assembleCp0 [ .puxcpu 15 15 15 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble-valid-max failed: {e}")
    }
    ,
    { name := "unit/assemble/x-over-range"
      run := do
        -- [B9]
        match assembleCp0 [ .puxcpu 16 0 0 ] with
        | .ok _ => throw (IO.userError "x-over-range: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure () else throw (IO.userError s!"x-over-range: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/assemble/y-over-range"
      run := do
        -- [B9]
        match assembleCp0 [ .puxcpu 0 16 0 ] with
        | .ok _ => throw (IO.userError "y-over-range: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure () else throw (IO.userError s!"y-over-range: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/assemble/z-over-range"
      run := do
        -- [B9]
        match assembleCp0 [ .puxcpu 0 0 16 ] with
        | .ok _ => throw (IO.userError "z-over-range: expected rangeChk")
        | .error e =>
            if e = .rangeChk then pure () else throw (IO.userError s!"z-over-range: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/decode/round-trip"
      run := do
        -- [B10]
        match decodePuxcpu 3 4 5 with
        | .ok (.puxcpu 3 4 5, bits, _) =>
            if bits ≠ 24 then
              throw (IO.userError s!"decode-round-trip bits={bits}")
            else
              pure ()
        | .ok (i, _, _) => throw (IO.userError s!"decode-round-trip got {reprStr i}")
        | .error e => throw (IO.userError s!"decode-round-trip error {e}")
    }
    ,
    { name := "unit/decode/neighbor-544"
      run := do
        -- [B11]
        match decodePuxc2 1 2 3 with
        | .ok (.puxc2 1 2 3, _, _) => pure ()
        | .ok (i, _, _) => throw (IO.userError s!"decode-neighbor-544 expected pucx2, got {reprStr i}")
        | .error e => throw (IO.userError s!"decode-neighbor-544 error {e}")
    }
    ,
    { name := "unit/decode/neighbor-546"
      run := do
        -- [B11]
        match decodePu2xc 5 6 7 with
        | .ok (.pu2xc 5 6 7, _, _) => pure ()
        | .ok (i, _, _) => throw (IO.userError s!"decode-neighbor-546 expected pu2xc, got {reprStr i}")
        | .error e => throw (IO.userError s!"decode-neighbor-546 error {e}")
    }
    ,
    { name := "unit/decode/truncated-8"
      run := do
        -- [B12]
        match decodeCp0WithBits (Slice.ofCell truncated8Code) with
        | .error .invOpcode => pure ()
        | .ok (instr, bits, _) => throw (IO.userError s!"decode-8 expected invOpcode, got {reprStr instr} {bits}")
        | .error e => throw (IO.userError s!"decode-8 expected invOpcode, got {e}")
    }
    ,
    { name := "unit/decode/truncated-15"
      run := do
        -- [B12]
        match decodeCp0WithBits (Slice.ofCell truncated15Code) with
        | .error .invOpcode => pure ()
        | .ok (instr, bits, _) => throw (IO.userError s!"decode-15 expected invOpcode, got {reprStr instr} {bits}")
        | .error e => throw (IO.userError s!"decode-15 expected invOpcode, got {e}")
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "ok/size1-baseline" 0 0 0 (makeStack 1),
    mkCase "ok/size1-nonint" 0 0 0 (#[.null]),
    mkCase "ok/size2-x0-y0-z1" 0 0 1 (makeStack 2),
    mkCase "ok/size2-x1-y0-z1" 1 0 1 (makeStack 2),
    mkCase "ok/size2-x1-y2-z0" 1 2 0 (makeStack 2),
    mkCase "ok/size2-x1-y2-z1" 1 2 1 (makeStack 2),
    mkCase "ok/size3-x0-y2-z1" 0 2 1 (makeStack 3),
    mkCase "ok/size3-x1-y1-z3" 1 1 3 (makeStack 3),
    mkCase "ok/size3-x2-y1-z3" 2 1 3 (makeStack 3),
    mkCase "ok/size3-x2-y3-z2" 2 3 2 (makeStack 3),
    mkCase "ok/size4-x0-y4-z0" 0 4 0 (makeStack 4),
    mkCase "ok/size4-x3-y0-z4" 3 0 4 (makeStack 4),
    mkCase "ok/size4-x3-y4-z4" 3 4 4 (makeStack 4),
    mkCase "ok/size5-x0-y5-z5" 0 5 5 (makeStack 5),
    mkCase "ok/size5-x4-y3-z5" 4 3 5 (makeStack 5),
    mkCase "ok/size6-x5-y0-z6" 5 0 6 (makeStack 6),
    mkCase "ok/size6-x0-y6-z2" 0 6 2 (makeStack 6),
    mkCase "ok/size16-x15-y15-z15" 15 15 15 (makeStack 16),
    mkCase "ok/size16-x0-y15-z15" 0 15 15 (makeStack 16),
    mkCase "ok/size16-x15-y8-z15" 15 8 15 (makeStack 16),
    mkCase "ok/nonint-stack" 0 1 2 #[intV 10, intV 11, .null, .cell refCell],
    mkCase "ok/nonint-stack-deep" 2 9 6 #[.null, .builder Builder.empty, .tuple #[], intV 9, intV 10],

    -- [B3]
    mkCase "err/x-underflow-empty" 0 0 0 #[],
    mkCase "err/x-underflow-size1" 1 0 0 (makeStack 1),
    mkCase "err/x-underflow-size2" 2 1 1 (makeStack 2),
    mkCase "err/x-underflow-size16" 16 5 3 (makeStack 16),

    -- [B4]
    mkCase "err/y-underflow-size1" 0 3 0 (makeStack 1),
    mkCase "err/y-underflow-size2" 1 3 1 (makeStack 2),
    mkCase "err/y-underflow-size5" 4 6 4 (makeStack 5),

    -- [B5]
    mkCase "err/z-underflow-size1" 0 0 2 (makeStack 1),
    mkCase "err/z-underflow-size3" 1 1 4 (makeStack 3),
    mkCase "err/z-underflow-size10" 1 2 12 (makeStack 10),

    -- [B7]
    mkCase "ok/alias-x-y" 1 1 2 (makeStack 6),
    mkCase "ok/alias-x-z" 3 5 3 (makeStack 8),
    mkCase "ok/alias-y-z" 0 5 5 (makeStack 8),
    mkCase "ok/alias-all-equal" 2 2 2 (makeStack 7),

    -- [B8]
    mkCase "ok/x0-boundary-depth" 0 8 8 (makeStack 9),
    mkCase "ok/y-depth-boundary" 5 9 4 (makeStack 9),
    mkCase "ok/z-depth-boundary" 5 4 9 (makeStack 9),

    -- [B10]
    mkCase "ok/decode-raw" 3 4 5 #[],

    -- [B11]
    mkCaseCode "decode-raw-neighbor-544" (makeStack 3) puxc2RawCode,
    mkCaseCode "decode-raw-neighbor-546" (makeStack 3) pu2xcRawCode,
    mkCaseCode "decode-err-truncated-8" #[] truncated8Code,
    mkCaseCode "decode-err-truncated-15" #[] truncated15Code,

    -- [B13]
    { name := "gas/exact-cost-succeeds"
      instr := puxcpuId
      program := #[.puxcpu 0 0 0]
      initStack := makeStack 1
      gasLimits := oracleGasLimitsExact gasExact },
    { name := "gas/exact-minus-one-fails"
      instr := puxcpuId
      program := #[.puxcpu 0 0 0]
      initStack := makeStack 1
      gasLimits := oracleGasLimitsExactMinusOne gasExactMinusOne }
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr puxcpuId
      count := 500
      gen := genPuxcpuFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUXCPU
